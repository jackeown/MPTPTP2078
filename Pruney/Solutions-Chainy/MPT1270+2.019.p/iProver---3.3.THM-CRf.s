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
% DateTime   : Thu Dec  3 12:15:17 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 691 expanded)
%              Number of clauses        :   96 ( 248 expanded)
%              Number of leaves         :   18 ( 155 expanded)
%              Depth                    :   23
%              Number of atoms          :  386 (2779 expanded)
%              Number of equality atoms :  141 ( 324 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK1,k2_tops_1(X0,sK1))
          | ~ v2_tops_1(sK1,X0) )
        & ( r1_tarski(sK1,k2_tops_1(X0,sK1))
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f51,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_154,plain,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_468,plain,
    ( v2_tops_1(sK1,sK0)
    | r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | k2_tops_1(sK0,sK1) != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_154])).

cnf(c_469,plain,
    ( v2_tops_1(sK1,sK0)
    | r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1))) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_14,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_354,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_355,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(sK1,k4_xboole_0(X1,k2_tops_1(sK0,sK1)))
    | k1_tops_1(sK0,X0) = k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_469,c_355])).

cnf(c_572,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_576,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_17])).

cnf(c_1222,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1238,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2582,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,k2_tops_1(sK0,sK1)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1238])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1233,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6248,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k4_xboole_0(k4_xboole_0(X0,k2_tops_1(sK0,sK1)),sK1) = k4_xboole_0(X0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2582,c_1233])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_792,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1587,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_1592,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3284,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3289,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3284])).

cnf(c_1231,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_1230,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_1684,plain,
    ( k4_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1233])).

cnf(c_1964,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1231,c_1684])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_152,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_502,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) != X0
    | k1_tops_1(sK0,X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_152,c_397])).

cnf(c_503,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != sK1 ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_556,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1)))
    | k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != sK1 ),
    inference(resolution,[status(thm)],[c_469,c_503])).

cnf(c_789,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_556])).

cnf(c_1224,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1))) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_4630,plain,
    ( r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1964,c_1224])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_60,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_62,plain,
    ( r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_813,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_794,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1440,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,k1_xboole_0)
    | X0 != X2
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_2115,plain,
    ( r1_xboole_0(X0,k1_tops_1(sK0,sK1))
    | ~ r1_xboole_0(X1,k1_xboole_0)
    | X0 != X1
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_2116,plain,
    ( X0 != X1
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | r1_xboole_0(X0,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2115])).

cnf(c_2118,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK1 != sK1
    | r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_xboole_0(sK1,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2116])).

cnf(c_2436,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1964,c_1222])).

cnf(c_5309,plain,
    ( r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4630,c_62,c_813,c_2118,c_2436])).

cnf(c_5314,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5309,c_1238])).

cnf(c_5995,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5314,c_1233])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | X0 != X3
    | k1_tops_1(sK0,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_397])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(k1_tops_1(sK0,X0),k4_xboole_0(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_1227,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,X0),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_6203,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5995,c_1227])).

cnf(c_793,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1438,plain,
    ( k1_tops_1(sK0,sK1) != X0
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_11056,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1438])).

cnf(c_13532,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6248,c_20,c_1592,c_3289,c_6203,c_11056])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_1229,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_1469,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1231,c_1229])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_1228,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1232,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2637,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1232])).

cnf(c_3152,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_1231,c_2637])).

cnf(c_3165,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1469,c_3152])).

cnf(c_13549,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_13532,c_3165])).

cnf(c_1237,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1683,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1237,c_1233])).

cnf(c_13567,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_13549,c_1683])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_515,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != k2_tops_1(sK0,sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_152,c_421])).

cnf(c_516,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK1) != k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_518,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k2_pre_topc(sK0,sK1) != k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_17])).

cnf(c_13,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_369,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_370,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) != k2_pre_topc(sK0,sK1)
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_518,c_370])).

cnf(c_590,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) != k2_pre_topc(sK0,sK1)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13567,c_11056,c_6203,c_3289,c_1592,c_590,c_20,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 13:07:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.50/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/0.98  
% 3.50/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/0.98  
% 3.50/0.98  ------  iProver source info
% 3.50/0.98  
% 3.50/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.50/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/0.98  git: non_committed_changes: false
% 3.50/0.98  git: last_make_outside_of_git: false
% 3.50/0.98  
% 3.50/0.98  ------ 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options
% 3.50/0.98  
% 3.50/0.98  --out_options                           all
% 3.50/0.98  --tptp_safe_out                         true
% 3.50/0.98  --problem_path                          ""
% 3.50/0.98  --include_path                          ""
% 3.50/0.98  --clausifier                            res/vclausify_rel
% 3.50/0.98  --clausifier_options                    --mode clausify
% 3.50/0.98  --stdin                                 false
% 3.50/0.98  --stats_out                             all
% 3.50/0.98  
% 3.50/0.98  ------ General Options
% 3.50/0.98  
% 3.50/0.98  --fof                                   false
% 3.50/0.98  --time_out_real                         305.
% 3.50/0.98  --time_out_virtual                      -1.
% 3.50/0.98  --symbol_type_check                     false
% 3.50/0.98  --clausify_out                          false
% 3.50/0.98  --sig_cnt_out                           false
% 3.50/0.98  --trig_cnt_out                          false
% 3.50/0.98  --trig_cnt_out_tolerance                1.
% 3.50/0.98  --trig_cnt_out_sk_spl                   false
% 3.50/0.98  --abstr_cl_out                          false
% 3.50/0.98  
% 3.50/0.98  ------ Global Options
% 3.50/0.98  
% 3.50/0.98  --schedule                              default
% 3.50/0.98  --add_important_lit                     false
% 3.50/0.98  --prop_solver_per_cl                    1000
% 3.50/0.98  --min_unsat_core                        false
% 3.50/0.98  --soft_assumptions                      false
% 3.50/0.98  --soft_lemma_size                       3
% 3.50/0.98  --prop_impl_unit_size                   0
% 3.50/0.98  --prop_impl_unit                        []
% 3.50/0.98  --share_sel_clauses                     true
% 3.50/0.98  --reset_solvers                         false
% 3.50/0.98  --bc_imp_inh                            [conj_cone]
% 3.50/0.98  --conj_cone_tolerance                   3.
% 3.50/0.98  --extra_neg_conj                        none
% 3.50/0.98  --large_theory_mode                     true
% 3.50/0.98  --prolific_symb_bound                   200
% 3.50/0.98  --lt_threshold                          2000
% 3.50/0.98  --clause_weak_htbl                      true
% 3.50/0.98  --gc_record_bc_elim                     false
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing Options
% 3.50/0.98  
% 3.50/0.98  --preprocessing_flag                    true
% 3.50/0.98  --time_out_prep_mult                    0.1
% 3.50/0.98  --splitting_mode                        input
% 3.50/0.98  --splitting_grd                         true
% 3.50/0.98  --splitting_cvd                         false
% 3.50/0.98  --splitting_cvd_svl                     false
% 3.50/0.98  --splitting_nvd                         32
% 3.50/0.98  --sub_typing                            true
% 3.50/0.98  --prep_gs_sim                           true
% 3.50/0.98  --prep_unflatten                        true
% 3.50/0.98  --prep_res_sim                          true
% 3.50/0.98  --prep_upred                            true
% 3.50/0.98  --prep_sem_filter                       exhaustive
% 3.50/0.98  --prep_sem_filter_out                   false
% 3.50/0.98  --pred_elim                             true
% 3.50/0.98  --res_sim_input                         true
% 3.50/0.98  --eq_ax_congr_red                       true
% 3.50/0.98  --pure_diseq_elim                       true
% 3.50/0.98  --brand_transform                       false
% 3.50/0.98  --non_eq_to_eq                          false
% 3.50/0.98  --prep_def_merge                        true
% 3.50/0.98  --prep_def_merge_prop_impl              false
% 3.50/0.98  --prep_def_merge_mbd                    true
% 3.50/0.98  --prep_def_merge_tr_red                 false
% 3.50/0.98  --prep_def_merge_tr_cl                  false
% 3.50/0.98  --smt_preprocessing                     true
% 3.50/0.98  --smt_ac_axioms                         fast
% 3.50/0.98  --preprocessed_out                      false
% 3.50/0.98  --preprocessed_stats                    false
% 3.50/0.98  
% 3.50/0.98  ------ Abstraction refinement Options
% 3.50/0.98  
% 3.50/0.98  --abstr_ref                             []
% 3.50/0.98  --abstr_ref_prep                        false
% 3.50/0.98  --abstr_ref_until_sat                   false
% 3.50/0.98  --abstr_ref_sig_restrict                funpre
% 3.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.98  --abstr_ref_under                       []
% 3.50/0.98  
% 3.50/0.98  ------ SAT Options
% 3.50/0.98  
% 3.50/0.98  --sat_mode                              false
% 3.50/0.98  --sat_fm_restart_options                ""
% 3.50/0.98  --sat_gr_def                            false
% 3.50/0.98  --sat_epr_types                         true
% 3.50/0.98  --sat_non_cyclic_types                  false
% 3.50/0.98  --sat_finite_models                     false
% 3.50/0.98  --sat_fm_lemmas                         false
% 3.50/0.98  --sat_fm_prep                           false
% 3.50/0.98  --sat_fm_uc_incr                        true
% 3.50/0.98  --sat_out_model                         small
% 3.50/0.98  --sat_out_clauses                       false
% 3.50/0.98  
% 3.50/0.98  ------ QBF Options
% 3.50/0.98  
% 3.50/0.98  --qbf_mode                              false
% 3.50/0.98  --qbf_elim_univ                         false
% 3.50/0.98  --qbf_dom_inst                          none
% 3.50/0.98  --qbf_dom_pre_inst                      false
% 3.50/0.98  --qbf_sk_in                             false
% 3.50/0.98  --qbf_pred_elim                         true
% 3.50/0.98  --qbf_split                             512
% 3.50/0.98  
% 3.50/0.98  ------ BMC1 Options
% 3.50/0.98  
% 3.50/0.98  --bmc1_incremental                      false
% 3.50/0.98  --bmc1_axioms                           reachable_all
% 3.50/0.98  --bmc1_min_bound                        0
% 3.50/0.98  --bmc1_max_bound                        -1
% 3.50/0.98  --bmc1_max_bound_default                -1
% 3.50/0.98  --bmc1_symbol_reachability              true
% 3.50/0.98  --bmc1_property_lemmas                  false
% 3.50/0.98  --bmc1_k_induction                      false
% 3.50/0.98  --bmc1_non_equiv_states                 false
% 3.50/0.98  --bmc1_deadlock                         false
% 3.50/0.98  --bmc1_ucm                              false
% 3.50/0.98  --bmc1_add_unsat_core                   none
% 3.50/0.98  --bmc1_unsat_core_children              false
% 3.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.98  --bmc1_out_stat                         full
% 3.50/0.98  --bmc1_ground_init                      false
% 3.50/0.98  --bmc1_pre_inst_next_state              false
% 3.50/0.98  --bmc1_pre_inst_state                   false
% 3.50/0.98  --bmc1_pre_inst_reach_state             false
% 3.50/0.98  --bmc1_out_unsat_core                   false
% 3.50/0.98  --bmc1_aig_witness_out                  false
% 3.50/0.98  --bmc1_verbose                          false
% 3.50/0.98  --bmc1_dump_clauses_tptp                false
% 3.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.98  --bmc1_dump_file                        -
% 3.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.98  --bmc1_ucm_extend_mode                  1
% 3.50/0.98  --bmc1_ucm_init_mode                    2
% 3.50/0.98  --bmc1_ucm_cone_mode                    none
% 3.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.98  --bmc1_ucm_relax_model                  4
% 3.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.98  --bmc1_ucm_layered_model                none
% 3.50/0.98  --bmc1_ucm_max_lemma_size               10
% 3.50/0.98  
% 3.50/0.98  ------ AIG Options
% 3.50/0.98  
% 3.50/0.98  --aig_mode                              false
% 3.50/0.98  
% 3.50/0.98  ------ Instantiation Options
% 3.50/0.98  
% 3.50/0.98  --instantiation_flag                    true
% 3.50/0.98  --inst_sos_flag                         false
% 3.50/0.98  --inst_sos_phase                        true
% 3.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel_side                     num_symb
% 3.50/0.98  --inst_solver_per_active                1400
% 3.50/0.98  --inst_solver_calls_frac                1.
% 3.50/0.98  --inst_passive_queue_type               priority_queues
% 3.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.98  --inst_passive_queues_freq              [25;2]
% 3.50/0.98  --inst_dismatching                      true
% 3.50/0.98  --inst_eager_unprocessed_to_passive     true
% 3.50/0.98  --inst_prop_sim_given                   true
% 3.50/0.98  --inst_prop_sim_new                     false
% 3.50/0.98  --inst_subs_new                         false
% 3.50/0.98  --inst_eq_res_simp                      false
% 3.50/0.98  --inst_subs_given                       false
% 3.50/0.98  --inst_orphan_elimination               true
% 3.50/0.98  --inst_learning_loop_flag               true
% 3.50/0.98  --inst_learning_start                   3000
% 3.50/0.98  --inst_learning_factor                  2
% 3.50/0.98  --inst_start_prop_sim_after_learn       3
% 3.50/0.98  --inst_sel_renew                        solver
% 3.50/0.98  --inst_lit_activity_flag                true
% 3.50/0.98  --inst_restr_to_given                   false
% 3.50/0.98  --inst_activity_threshold               500
% 3.50/0.98  --inst_out_proof                        true
% 3.50/0.98  
% 3.50/0.98  ------ Resolution Options
% 3.50/0.98  
% 3.50/0.98  --resolution_flag                       true
% 3.50/0.98  --res_lit_sel                           adaptive
% 3.50/0.98  --res_lit_sel_side                      none
% 3.50/0.98  --res_ordering                          kbo
% 3.50/0.98  --res_to_prop_solver                    active
% 3.50/0.98  --res_prop_simpl_new                    false
% 3.50/0.98  --res_prop_simpl_given                  true
% 3.50/0.98  --res_passive_queue_type                priority_queues
% 3.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.98  --res_passive_queues_freq               [15;5]
% 3.50/0.98  --res_forward_subs                      full
% 3.50/0.98  --res_backward_subs                     full
% 3.50/0.98  --res_forward_subs_resolution           true
% 3.50/0.98  --res_backward_subs_resolution          true
% 3.50/0.98  --res_orphan_elimination                true
% 3.50/0.98  --res_time_limit                        2.
% 3.50/0.98  --res_out_proof                         true
% 3.50/0.98  
% 3.50/0.98  ------ Superposition Options
% 3.50/0.98  
% 3.50/0.98  --superposition_flag                    true
% 3.50/0.98  --sup_passive_queue_type                priority_queues
% 3.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.98  --demod_completeness_check              fast
% 3.50/0.98  --demod_use_ground                      true
% 3.50/0.98  --sup_to_prop_solver                    passive
% 3.50/0.98  --sup_prop_simpl_new                    true
% 3.50/0.98  --sup_prop_simpl_given                  true
% 3.50/0.98  --sup_fun_splitting                     false
% 3.50/0.98  --sup_smt_interval                      50000
% 3.50/0.98  
% 3.50/0.98  ------ Superposition Simplification Setup
% 3.50/0.98  
% 3.50/0.98  --sup_indices_passive                   []
% 3.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_full_bw                           [BwDemod]
% 3.50/0.98  --sup_immed_triv                        [TrivRules]
% 3.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_immed_bw_main                     []
% 3.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.98  
% 3.50/0.98  ------ Combination Options
% 3.50/0.98  
% 3.50/0.98  --comb_res_mult                         3
% 3.50/0.98  --comb_sup_mult                         2
% 3.50/0.98  --comb_inst_mult                        10
% 3.50/0.98  
% 3.50/0.98  ------ Debug Options
% 3.50/0.98  
% 3.50/0.98  --dbg_backtrace                         false
% 3.50/0.98  --dbg_dump_prop_clauses                 false
% 3.50/0.98  --dbg_dump_prop_clauses_file            -
% 3.50/0.98  --dbg_out_stat                          false
% 3.50/0.98  ------ Parsing...
% 3.50/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.98  ------ Proving...
% 3.50/0.98  ------ Problem Properties 
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  clauses                                 19
% 3.50/0.98  conjectures                             1
% 3.50/0.98  EPR                                     4
% 3.50/0.98  Horn                                    18
% 3.50/0.98  unary                                   3
% 3.50/0.98  binary                                  14
% 3.50/0.98  lits                                    37
% 3.50/0.98  lits eq                                 12
% 3.50/0.98  fd_pure                                 0
% 3.50/0.98  fd_pseudo                               0
% 3.50/0.98  fd_cond                                 1
% 3.50/0.98  fd_pseudo_cond                          0
% 3.50/0.98  AC symbols                              0
% 3.50/0.98  
% 3.50/0.98  ------ Schedule dynamic 5 is on 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  ------ 
% 3.50/0.98  Current options:
% 3.50/0.98  ------ 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options
% 3.50/0.98  
% 3.50/0.98  --out_options                           all
% 3.50/0.98  --tptp_safe_out                         true
% 3.50/0.98  --problem_path                          ""
% 3.50/0.98  --include_path                          ""
% 3.50/0.98  --clausifier                            res/vclausify_rel
% 3.50/0.98  --clausifier_options                    --mode clausify
% 3.50/0.98  --stdin                                 false
% 3.50/0.98  --stats_out                             all
% 3.50/0.98  
% 3.50/0.98  ------ General Options
% 3.50/0.98  
% 3.50/0.98  --fof                                   false
% 3.50/0.98  --time_out_real                         305.
% 3.50/0.98  --time_out_virtual                      -1.
% 3.50/0.98  --symbol_type_check                     false
% 3.50/0.98  --clausify_out                          false
% 3.50/0.98  --sig_cnt_out                           false
% 3.50/0.98  --trig_cnt_out                          false
% 3.50/0.98  --trig_cnt_out_tolerance                1.
% 3.50/0.98  --trig_cnt_out_sk_spl                   false
% 3.50/0.98  --abstr_cl_out                          false
% 3.50/0.98  
% 3.50/0.98  ------ Global Options
% 3.50/0.98  
% 3.50/0.98  --schedule                              default
% 3.50/0.98  --add_important_lit                     false
% 3.50/0.98  --prop_solver_per_cl                    1000
% 3.50/0.98  --min_unsat_core                        false
% 3.50/0.98  --soft_assumptions                      false
% 3.50/0.98  --soft_lemma_size                       3
% 3.50/0.98  --prop_impl_unit_size                   0
% 3.50/0.98  --prop_impl_unit                        []
% 3.50/0.98  --share_sel_clauses                     true
% 3.50/0.98  --reset_solvers                         false
% 3.50/0.98  --bc_imp_inh                            [conj_cone]
% 3.50/0.98  --conj_cone_tolerance                   3.
% 3.50/0.98  --extra_neg_conj                        none
% 3.50/0.98  --large_theory_mode                     true
% 3.50/0.98  --prolific_symb_bound                   200
% 3.50/0.98  --lt_threshold                          2000
% 3.50/0.98  --clause_weak_htbl                      true
% 3.50/0.98  --gc_record_bc_elim                     false
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing Options
% 3.50/0.98  
% 3.50/0.98  --preprocessing_flag                    true
% 3.50/0.98  --time_out_prep_mult                    0.1
% 3.50/0.98  --splitting_mode                        input
% 3.50/0.98  --splitting_grd                         true
% 3.50/0.98  --splitting_cvd                         false
% 3.50/0.98  --splitting_cvd_svl                     false
% 3.50/0.98  --splitting_nvd                         32
% 3.50/0.98  --sub_typing                            true
% 3.50/0.98  --prep_gs_sim                           true
% 3.50/0.98  --prep_unflatten                        true
% 3.50/0.98  --prep_res_sim                          true
% 3.50/0.98  --prep_upred                            true
% 3.50/0.98  --prep_sem_filter                       exhaustive
% 3.50/0.98  --prep_sem_filter_out                   false
% 3.50/0.98  --pred_elim                             true
% 3.50/0.98  --res_sim_input                         true
% 3.50/0.98  --eq_ax_congr_red                       true
% 3.50/0.98  --pure_diseq_elim                       true
% 3.50/0.98  --brand_transform                       false
% 3.50/0.98  --non_eq_to_eq                          false
% 3.50/0.98  --prep_def_merge                        true
% 3.50/0.98  --prep_def_merge_prop_impl              false
% 3.50/0.98  --prep_def_merge_mbd                    true
% 3.50/0.98  --prep_def_merge_tr_red                 false
% 3.50/0.98  --prep_def_merge_tr_cl                  false
% 3.50/0.98  --smt_preprocessing                     true
% 3.50/0.98  --smt_ac_axioms                         fast
% 3.50/0.98  --preprocessed_out                      false
% 3.50/0.98  --preprocessed_stats                    false
% 3.50/0.98  
% 3.50/0.98  ------ Abstraction refinement Options
% 3.50/0.98  
% 3.50/0.98  --abstr_ref                             []
% 3.50/0.98  --abstr_ref_prep                        false
% 3.50/0.98  --abstr_ref_until_sat                   false
% 3.50/0.98  --abstr_ref_sig_restrict                funpre
% 3.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.98  --abstr_ref_under                       []
% 3.50/0.98  
% 3.50/0.98  ------ SAT Options
% 3.50/0.98  
% 3.50/0.98  --sat_mode                              false
% 3.50/0.98  --sat_fm_restart_options                ""
% 3.50/0.98  --sat_gr_def                            false
% 3.50/0.98  --sat_epr_types                         true
% 3.50/0.98  --sat_non_cyclic_types                  false
% 3.50/0.98  --sat_finite_models                     false
% 3.50/0.98  --sat_fm_lemmas                         false
% 3.50/0.98  --sat_fm_prep                           false
% 3.50/0.98  --sat_fm_uc_incr                        true
% 3.50/0.98  --sat_out_model                         small
% 3.50/0.98  --sat_out_clauses                       false
% 3.50/0.98  
% 3.50/0.98  ------ QBF Options
% 3.50/0.98  
% 3.50/0.98  --qbf_mode                              false
% 3.50/0.98  --qbf_elim_univ                         false
% 3.50/0.98  --qbf_dom_inst                          none
% 3.50/0.98  --qbf_dom_pre_inst                      false
% 3.50/0.98  --qbf_sk_in                             false
% 3.50/0.98  --qbf_pred_elim                         true
% 3.50/0.98  --qbf_split                             512
% 3.50/0.98  
% 3.50/0.98  ------ BMC1 Options
% 3.50/0.98  
% 3.50/0.98  --bmc1_incremental                      false
% 3.50/0.98  --bmc1_axioms                           reachable_all
% 3.50/0.98  --bmc1_min_bound                        0
% 3.50/0.98  --bmc1_max_bound                        -1
% 3.50/0.98  --bmc1_max_bound_default                -1
% 3.50/0.98  --bmc1_symbol_reachability              true
% 3.50/0.98  --bmc1_property_lemmas                  false
% 3.50/0.98  --bmc1_k_induction                      false
% 3.50/0.98  --bmc1_non_equiv_states                 false
% 3.50/0.98  --bmc1_deadlock                         false
% 3.50/0.98  --bmc1_ucm                              false
% 3.50/0.98  --bmc1_add_unsat_core                   none
% 3.50/0.98  --bmc1_unsat_core_children              false
% 3.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.98  --bmc1_out_stat                         full
% 3.50/0.98  --bmc1_ground_init                      false
% 3.50/0.98  --bmc1_pre_inst_next_state              false
% 3.50/0.98  --bmc1_pre_inst_state                   false
% 3.50/0.98  --bmc1_pre_inst_reach_state             false
% 3.50/0.98  --bmc1_out_unsat_core                   false
% 3.50/0.98  --bmc1_aig_witness_out                  false
% 3.50/0.98  --bmc1_verbose                          false
% 3.50/0.98  --bmc1_dump_clauses_tptp                false
% 3.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.98  --bmc1_dump_file                        -
% 3.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.98  --bmc1_ucm_extend_mode                  1
% 3.50/0.98  --bmc1_ucm_init_mode                    2
% 3.50/0.98  --bmc1_ucm_cone_mode                    none
% 3.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.98  --bmc1_ucm_relax_model                  4
% 3.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.98  --bmc1_ucm_layered_model                none
% 3.50/0.98  --bmc1_ucm_max_lemma_size               10
% 3.50/0.98  
% 3.50/0.98  ------ AIG Options
% 3.50/0.98  
% 3.50/0.98  --aig_mode                              false
% 3.50/0.98  
% 3.50/0.98  ------ Instantiation Options
% 3.50/0.98  
% 3.50/0.98  --instantiation_flag                    true
% 3.50/0.98  --inst_sos_flag                         false
% 3.50/0.98  --inst_sos_phase                        true
% 3.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel_side                     none
% 3.50/0.98  --inst_solver_per_active                1400
% 3.50/0.98  --inst_solver_calls_frac                1.
% 3.50/0.98  --inst_passive_queue_type               priority_queues
% 3.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.98  --inst_passive_queues_freq              [25;2]
% 3.50/0.98  --inst_dismatching                      true
% 3.50/0.98  --inst_eager_unprocessed_to_passive     true
% 3.50/0.98  --inst_prop_sim_given                   true
% 3.50/0.98  --inst_prop_sim_new                     false
% 3.50/0.98  --inst_subs_new                         false
% 3.50/0.98  --inst_eq_res_simp                      false
% 3.50/0.98  --inst_subs_given                       false
% 3.50/0.98  --inst_orphan_elimination               true
% 3.50/0.98  --inst_learning_loop_flag               true
% 3.50/0.98  --inst_learning_start                   3000
% 3.50/0.98  --inst_learning_factor                  2
% 3.50/0.98  --inst_start_prop_sim_after_learn       3
% 3.50/0.98  --inst_sel_renew                        solver
% 3.50/0.98  --inst_lit_activity_flag                true
% 3.50/0.98  --inst_restr_to_given                   false
% 3.50/0.98  --inst_activity_threshold               500
% 3.50/0.98  --inst_out_proof                        true
% 3.50/0.98  
% 3.50/0.98  ------ Resolution Options
% 3.50/0.98  
% 3.50/0.98  --resolution_flag                       false
% 3.50/0.98  --res_lit_sel                           adaptive
% 3.50/0.98  --res_lit_sel_side                      none
% 3.50/0.98  --res_ordering                          kbo
% 3.50/0.99  --res_to_prop_solver                    active
% 3.50/0.99  --res_prop_simpl_new                    false
% 3.50/0.99  --res_prop_simpl_given                  true
% 3.50/0.99  --res_passive_queue_type                priority_queues
% 3.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.99  --res_passive_queues_freq               [15;5]
% 3.50/0.99  --res_forward_subs                      full
% 3.50/0.99  --res_backward_subs                     full
% 3.50/0.99  --res_forward_subs_resolution           true
% 3.50/0.99  --res_backward_subs_resolution          true
% 3.50/0.99  --res_orphan_elimination                true
% 3.50/0.99  --res_time_limit                        2.
% 3.50/0.99  --res_out_proof                         true
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Options
% 3.50/0.99  
% 3.50/0.99  --superposition_flag                    true
% 3.50/0.99  --sup_passive_queue_type                priority_queues
% 3.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.99  --demod_completeness_check              fast
% 3.50/0.99  --demod_use_ground                      true
% 3.50/0.99  --sup_to_prop_solver                    passive
% 3.50/0.99  --sup_prop_simpl_new                    true
% 3.50/0.99  --sup_prop_simpl_given                  true
% 3.50/0.99  --sup_fun_splitting                     false
% 3.50/0.99  --sup_smt_interval                      50000
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Simplification Setup
% 3.50/0.99  
% 3.50/0.99  --sup_indices_passive                   []
% 3.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_full_bw                           [BwDemod]
% 3.50/0.99  --sup_immed_triv                        [TrivRules]
% 3.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_immed_bw_main                     []
% 3.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  
% 3.50/0.99  ------ Combination Options
% 3.50/0.99  
% 3.50/0.99  --comb_res_mult                         3
% 3.50/0.99  --comb_sup_mult                         2
% 3.50/0.99  --comb_inst_mult                        10
% 3.50/0.99  
% 3.50/0.99  ------ Debug Options
% 3.50/0.99  
% 3.50/0.99  --dbg_backtrace                         false
% 3.50/0.99  --dbg_dump_prop_clauses                 false
% 3.50/0.99  --dbg_dump_prop_clauses_file            -
% 3.50/0.99  --dbg_out_stat                          false
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ Proving...
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS status Theorem for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  fof(f5,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f17,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.50/0.99    inference(ennf_transformation,[],[f5])).
% 3.50/0.99  
% 3.50/0.99  fof(f40,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f17])).
% 3.50/0.99  
% 3.50/0.99  fof(f13,conjecture,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f14,negated_conjecture,(
% 3.50/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.50/0.99    inference(negated_conjecture,[],[f13])).
% 3.50/0.99  
% 3.50/0.99  fof(f26,plain,(
% 3.50/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f14])).
% 3.50/0.99  
% 3.50/0.99  fof(f29,plain,(
% 3.50/0.99    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.50/0.99    inference(nnf_transformation,[],[f26])).
% 3.50/0.99  
% 3.50/0.99  fof(f30,plain,(
% 3.50/0.99    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.50/0.99    inference(flattening,[],[f29])).
% 3.50/0.99  
% 3.50/0.99  fof(f32,plain,(
% 3.50/0.99    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK1,k2_tops_1(X0,sK1)) | ~v2_tops_1(sK1,X0)) & (r1_tarski(sK1,k2_tops_1(X0,sK1)) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f31,plain,(
% 3.50/0.99    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f33,plain,(
% 3.50/0.99    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 3.50/0.99  
% 3.50/0.99  fof(f51,plain,(
% 3.50/0.99    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 3.50/0.99    inference(cnf_transformation,[],[f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f12,axiom,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f25,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f12])).
% 3.50/0.99  
% 3.50/0.99  fof(f28,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(nnf_transformation,[],[f25])).
% 3.50/0.99  
% 3.50/0.99  fof(f47,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f28])).
% 3.50/0.99  
% 3.50/0.99  fof(f49,plain,(
% 3.50/0.99    l1_pre_topc(sK0)),
% 3.50/0.99    inference(cnf_transformation,[],[f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f50,plain,(
% 3.50/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.50/0.99    inference(cnf_transformation,[],[f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f1,axiom,(
% 3.50/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f15,plain,(
% 3.50/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.50/0.99    inference(ennf_transformation,[],[f1])).
% 3.50/0.99  
% 3.50/0.99  fof(f34,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f15])).
% 3.50/0.99  
% 3.50/0.99  fof(f4,axiom,(
% 3.50/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f27,plain,(
% 3.50/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.50/0.99    inference(nnf_transformation,[],[f4])).
% 3.50/0.99  
% 3.50/0.99  fof(f38,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f27])).
% 3.50/0.99  
% 3.50/0.99  fof(f3,axiom,(
% 3.50/0.99    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f16,plain,(
% 3.50/0.99    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 3.50/0.99    inference(ennf_transformation,[],[f3])).
% 3.50/0.99  
% 3.50/0.99  fof(f37,plain,(
% 3.50/0.99    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 3.50/0.99    inference(cnf_transformation,[],[f16])).
% 3.50/0.99  
% 3.50/0.99  fof(f11,axiom,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f24,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f11])).
% 3.50/0.99  
% 3.50/0.99  fof(f46,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f24])).
% 3.50/0.99  
% 3.50/0.99  fof(f52,plain,(
% 3.50/0.99    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 3.50/0.99    inference(cnf_transformation,[],[f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f10,axiom,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f23,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f10])).
% 3.50/0.99  
% 3.50/0.99  fof(f45,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f23])).
% 3.50/0.99  
% 3.50/0.99  fof(f2,axiom,(
% 3.50/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f35,plain,(
% 3.50/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f2])).
% 3.50/0.99  
% 3.50/0.99  fof(f9,axiom,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f22,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f9])).
% 3.50/0.99  
% 3.50/0.99  fof(f44,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f22])).
% 3.50/0.99  
% 3.50/0.99  fof(f7,axiom,(
% 3.50/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f19,plain,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.50/0.99    inference(ennf_transformation,[],[f7])).
% 3.50/0.99  
% 3.50/0.99  fof(f20,plain,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(flattening,[],[f19])).
% 3.50/0.99  
% 3.50/0.99  fof(f42,plain,(
% 3.50/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f20])).
% 3.50/0.99  
% 3.50/0.99  fof(f6,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f18,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.50/0.99    inference(ennf_transformation,[],[f6])).
% 3.50/0.99  
% 3.50/0.99  fof(f41,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f18])).
% 3.50/0.99  
% 3.50/0.99  fof(f8,axiom,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f21,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f8])).
% 3.50/0.99  
% 3.50/0.99  fof(f43,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f21])).
% 3.50/0.99  
% 3.50/0.99  fof(f48,plain,(
% 3.50/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f28])).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_16,negated_conjecture,
% 3.50/0.99      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_154,plain,
% 3.50/0.99      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 3.50/0.99      inference(prop_impl,[status(thm)],[c_16]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_468,plain,
% 3.50/0.99      ( v2_tops_1(sK1,sK0)
% 3.50/0.99      | r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 3.50/0.99      | k2_tops_1(sK0,sK1) != X2
% 3.50/0.99      | sK1 != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_154]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_469,plain,
% 3.50/0.99      ( v2_tops_1(sK1,sK0)
% 3.50/0.99      | r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1))) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_468]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_14,plain,
% 3.50/0.99      ( ~ v2_tops_1(X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | ~ l1_pre_topc(X1)
% 3.50/0.99      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_18,negated_conjecture,
% 3.50/0.99      ( l1_pre_topc(sK0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_354,plain,
% 3.50/0.99      ( ~ v2_tops_1(X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | k1_tops_1(X1,X0) = k1_xboole_0
% 3.50/0.99      | sK0 != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_355,plain,
% 3.50/0.99      ( ~ v2_tops_1(X0,sK0)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_354]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_571,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | r1_xboole_0(sK1,k4_xboole_0(X1,k2_tops_1(sK0,sK1)))
% 3.50/0.99      | k1_tops_1(sK0,X0) = k1_xboole_0
% 3.50/0.99      | sK0 != sK0
% 3.50/0.99      | sK1 != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_469,c_355]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_572,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1)))
% 3.50/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_571]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_17,negated_conjecture,
% 3.50/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_576,plain,
% 3.50/0.99      ( r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1)))
% 3.50/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_572,c_17]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1222,plain,
% 3.50/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.50/0.99      | r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_0,plain,
% 3.50/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1238,plain,
% 3.50/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.50/0.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2582,plain,
% 3.50/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.50/0.99      | r1_xboole_0(k4_xboole_0(X0,k2_tops_1(sK0,sK1)),sK1) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1222,c_1238]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5,plain,
% 3.50/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1233,plain,
% 3.50/0.99      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6248,plain,
% 3.50/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.50/0.99      | k4_xboole_0(k4_xboole_0(X0,k2_tops_1(sK0,sK1)),sK1) = k4_xboole_0(X0,k2_tops_1(sK0,sK1)) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_2582,c_1233]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_20,plain,
% 3.50/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_792,plain,( X0 = X0 ),theory(equality) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1587,plain,
% 3.50/0.99      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X0) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_792]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1592,plain,
% 3.50/0.99      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1587]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2,plain,
% 3.50/0.99      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3284,plain,
% 3.50/0.99      ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
% 3.50/0.99      | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3289,plain,
% 3.50/0.99      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 3.50/0.99      | r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3284]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1231,plain,
% 3.50/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_12,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
% 3.50/0.99      | ~ l1_pre_topc(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_384,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
% 3.50/0.99      | sK0 != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_385,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_384]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1230,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.50/0.99      | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1684,plain,
% 3.50/0.99      ( k4_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1230,c_1233]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1964,plain,
% 3.50/0.99      ( k4_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1231,c_1684]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_15,negated_conjecture,
% 3.50/0.99      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_152,plain,
% 3.50/0.99      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 3.50/0.99      inference(prop_impl,[status(thm)],[c_15]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.50/0.99      | ~ l1_pre_topc(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_396,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.50/0.99      | sK0 != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_397,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_396]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_502,plain,
% 3.50/0.99      ( ~ v2_tops_1(sK1,sK0)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | k2_tops_1(sK0,sK1) != X0
% 3.50/0.99      | k1_tops_1(sK0,X0) != sK1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_152,c_397]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_503,plain,
% 3.50/0.99      ( ~ v2_tops_1(sK1,sK0)
% 3.50/0.99      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != sK1 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_502]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_556,plain,
% 3.50/0.99      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1)))
% 3.50/0.99      | k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != sK1 ),
% 3.50/0.99      inference(resolution,[status(thm)],[c_469,c_503]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_789,plain,
% 3.50/0.99      ( r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1)))
% 3.50/0.99      | ~ sP0_iProver_split ),
% 3.50/0.99      inference(splitting,
% 3.50/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.50/0.99                [c_556]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1224,plain,
% 3.50/0.99      ( r1_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1))) = iProver_top
% 3.50/0.99      | sP0_iProver_split != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4630,plain,
% 3.50/0.99      ( r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top
% 3.50/0.99      | sP0_iProver_split != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1964,c_1224]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1,plain,
% 3.50/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_60,plain,
% 3.50/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_62,plain,
% 3.50/0.99      ( r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_60]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_813,plain,
% 3.50/0.99      ( sK1 = sK1 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_792]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_794,plain,
% 3.50/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.50/0.99      theory(equality) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1440,plain,
% 3.50/0.99      ( r1_xboole_0(X0,X1)
% 3.50/0.99      | ~ r1_xboole_0(X2,k1_xboole_0)
% 3.50/0.99      | X0 != X2
% 3.50/0.99      | X1 != k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_794]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2115,plain,
% 3.50/0.99      ( r1_xboole_0(X0,k1_tops_1(sK0,sK1))
% 3.50/0.99      | ~ r1_xboole_0(X1,k1_xboole_0)
% 3.50/0.99      | X0 != X1
% 3.50/0.99      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1440]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2116,plain,
% 3.50/0.99      ( X0 != X1
% 3.50/0.99      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 3.50/0.99      | r1_xboole_0(X0,k1_tops_1(sK0,sK1)) = iProver_top
% 3.50/0.99      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2115]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2118,plain,
% 3.50/0.99      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 3.50/0.99      | sK1 != sK1
% 3.50/0.99      | r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top
% 3.50/0.99      | r1_xboole_0(sK1,k1_xboole_0) != iProver_top ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2116]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2436,plain,
% 3.50/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.50/0.99      | r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1964,c_1222]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5309,plain,
% 3.50/0.99      ( r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_4630,c_62,c_813,c_2118,c_2436]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5314,plain,
% 3.50/0.99      ( r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_5309,c_1238]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5995,plain,
% 3.50/0.99      ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_tops_1(sK0,sK1) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_5314,c_1233]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_478,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | r1_xboole_0(X1,k4_xboole_0(X2,X3))
% 3.50/0.99      | X0 != X3
% 3.50/0.99      | k1_tops_1(sK0,X0) != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_397]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_479,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | r1_xboole_0(k1_tops_1(sK0,X0),k4_xboole_0(X1,X0)) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_478]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1227,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.50/0.99      | r1_xboole_0(k1_tops_1(sK0,X0),k4_xboole_0(X1,X0)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6203,plain,
% 3.50/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.50/0.99      | r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_5995,c_1227]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_793,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1438,plain,
% 3.50/0.99      ( k1_tops_1(sK0,sK1) != X0
% 3.50/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.50/0.99      | k1_xboole_0 != X0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_793]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11056,plain,
% 3.50/0.99      ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
% 3.50/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.50/0.99      | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1438]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13532,plain,
% 3.50/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_6248,c_20,c_1592,c_3289,c_6203,c_11056]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | ~ l1_pre_topc(X1)
% 3.50/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_408,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 3.50/0.99      | sK0 != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_409,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_408]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1229,plain,
% 3.50/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1469,plain,
% 3.50/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1231,c_1229]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | ~ l1_pre_topc(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_432,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | sK0 != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_433,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_432]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1228,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.50/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.50/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.50/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1232,plain,
% 3.50/0.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2637,plain,
% 3.50/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1228,c_1232]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3152,plain,
% 3.50/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1231,c_2637]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3165,plain,
% 3.50/0.99      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1469,c_3152]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13549,plain,
% 3.50/0.99      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_13532,c_3165]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1237,plain,
% 3.50/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1683,plain,
% 3.50/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1237,c_1233]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13567,plain,
% 3.50/0.99      ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_13549,c_1683]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.50/0.99      | ~ l1_pre_topc(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_420,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.50/0.99      | sK0 != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_421,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_420]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_515,plain,
% 3.50/0.99      ( ~ v2_tops_1(sK1,sK0)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | k2_pre_topc(sK0,X0) != k2_tops_1(sK0,sK1)
% 3.50/0.99      | sK1 != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_152,c_421]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_516,plain,
% 3.50/0.99      ( ~ v2_tops_1(sK1,sK0)
% 3.50/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | k2_pre_topc(sK0,sK1) != k2_tops_1(sK0,sK1) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_515]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_518,plain,
% 3.50/0.99      ( ~ v2_tops_1(sK1,sK0)
% 3.50/0.99      | k2_pre_topc(sK0,sK1) != k2_tops_1(sK0,sK1) ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_516,c_17]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13,plain,
% 3.50/0.99      ( v2_tops_1(X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | ~ l1_pre_topc(X1)
% 3.50/0.99      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_369,plain,
% 3.50/0.99      ( v2_tops_1(X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | k1_tops_1(X1,X0) != k1_xboole_0
% 3.50/0.99      | sK0 != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_370,plain,
% 3.50/0.99      ( v2_tops_1(X0,sK0)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_369]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_589,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | k2_tops_1(sK0,sK1) != k2_pre_topc(sK0,sK1)
% 3.50/0.99      | k1_tops_1(sK0,X0) != k1_xboole_0
% 3.50/0.99      | sK0 != sK0
% 3.50/0.99      | sK1 != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_518,c_370]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_590,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.50/0.99      | k2_tops_1(sK0,sK1) != k2_pre_topc(sK0,sK1)
% 3.50/0.99      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_589]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(contradiction,plain,
% 3.50/0.99      ( $false ),
% 3.50/0.99      inference(minisat,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_13567,c_11056,c_6203,c_3289,c_1592,c_590,c_20,c_17]) ).
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  ------                               Statistics
% 3.50/0.99  
% 3.50/0.99  ------ General
% 3.50/0.99  
% 3.50/0.99  abstr_ref_over_cycles:                  0
% 3.50/0.99  abstr_ref_under_cycles:                 0
% 3.50/0.99  gc_basic_clause_elim:                   0
% 3.50/0.99  forced_gc_time:                         0
% 3.50/0.99  parsing_time:                           0.009
% 3.50/0.99  unif_index_cands_time:                  0.
% 3.50/0.99  unif_index_add_time:                    0.
% 3.50/0.99  orderings_time:                         0.
% 3.50/0.99  out_proof_time:                         0.01
% 3.50/0.99  total_time:                             0.406
% 3.50/0.99  num_of_symbols:                         47
% 3.50/0.99  num_of_terms:                           15055
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing
% 3.50/0.99  
% 3.50/0.99  num_of_splits:                          1
% 3.50/0.99  num_of_split_atoms:                     1
% 3.50/0.99  num_of_reused_defs:                     0
% 3.50/0.99  num_eq_ax_congr_red:                    8
% 3.50/0.99  num_of_sem_filtered_clauses:            1
% 3.50/0.99  num_of_subtypes:                        0
% 3.50/0.99  monotx_restored_types:                  0
% 3.50/0.99  sat_num_of_epr_types:                   0
% 3.50/0.99  sat_num_of_non_cyclic_types:            0
% 3.50/0.99  sat_guarded_non_collapsed_types:        0
% 3.50/0.99  num_pure_diseq_elim:                    0
% 3.50/0.99  simp_replaced_by:                       0
% 3.50/0.99  res_preprocessed:                       98
% 3.50/0.99  prep_upred:                             0
% 3.50/0.99  prep_unflattend:                        26
% 3.50/0.99  smt_new_axioms:                         0
% 3.50/0.99  pred_elim_cands:                        2
% 3.50/0.99  pred_elim:                              3
% 3.50/0.99  pred_elim_cl:                           1
% 3.50/0.99  pred_elim_cycles:                       6
% 3.50/0.99  merged_defs:                            10
% 3.50/0.99  merged_defs_ncl:                        0
% 3.50/0.99  bin_hyper_res:                          10
% 3.50/0.99  prep_cycles:                            4
% 3.50/0.99  pred_elim_time:                         0.007
% 3.50/0.99  splitting_time:                         0.
% 3.50/0.99  sem_filter_time:                        0.
% 3.50/0.99  monotx_time:                            0.
% 3.50/0.99  subtype_inf_time:                       0.
% 3.50/0.99  
% 3.50/0.99  ------ Problem properties
% 3.50/0.99  
% 3.50/0.99  clauses:                                19
% 3.50/0.99  conjectures:                            1
% 3.50/0.99  epr:                                    4
% 3.50/0.99  horn:                                   18
% 3.50/0.99  ground:                                 5
% 3.50/0.99  unary:                                  3
% 3.50/0.99  binary:                                 14
% 3.50/0.99  lits:                                   37
% 3.50/0.99  lits_eq:                                12
% 3.50/0.99  fd_pure:                                0
% 3.50/0.99  fd_pseudo:                              0
% 3.50/0.99  fd_cond:                                1
% 3.50/0.99  fd_pseudo_cond:                         0
% 3.50/0.99  ac_symbols:                             0
% 3.50/0.99  
% 3.50/0.99  ------ Propositional Solver
% 3.50/0.99  
% 3.50/0.99  prop_solver_calls:                      28
% 3.50/0.99  prop_fast_solver_calls:                 695
% 3.50/0.99  smt_solver_calls:                       0
% 3.50/0.99  smt_fast_solver_calls:                  0
% 3.50/0.99  prop_num_of_clauses:                    6254
% 3.50/0.99  prop_preprocess_simplified:             13660
% 3.50/0.99  prop_fo_subsumed:                       8
% 3.50/0.99  prop_solver_time:                       0.
% 3.50/0.99  smt_solver_time:                        0.
% 3.50/0.99  smt_fast_solver_time:                   0.
% 3.50/0.99  prop_fast_solver_time:                  0.
% 3.50/0.99  prop_unsat_core_time:                   0.
% 3.50/0.99  
% 3.50/0.99  ------ QBF
% 3.50/0.99  
% 3.50/0.99  qbf_q_res:                              0
% 3.50/0.99  qbf_num_tautologies:                    0
% 3.50/0.99  qbf_prep_cycles:                        0
% 3.50/0.99  
% 3.50/0.99  ------ BMC1
% 3.50/0.99  
% 3.50/0.99  bmc1_current_bound:                     -1
% 3.50/0.99  bmc1_last_solved_bound:                 -1
% 3.50/0.99  bmc1_unsat_core_size:                   -1
% 3.50/0.99  bmc1_unsat_core_parents_size:           -1
% 3.50/0.99  bmc1_merge_next_fun:                    0
% 3.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation
% 3.50/0.99  
% 3.50/0.99  inst_num_of_clauses:                    1869
% 3.50/0.99  inst_num_in_passive:                    609
% 3.50/0.99  inst_num_in_active:                     582
% 3.50/0.99  inst_num_in_unprocessed:                678
% 3.50/0.99  inst_num_of_loops:                      630
% 3.50/0.99  inst_num_of_learning_restarts:          0
% 3.50/0.99  inst_num_moves_active_passive:          46
% 3.50/0.99  inst_lit_activity:                      0
% 3.50/0.99  inst_lit_activity_moves:                0
% 3.50/0.99  inst_num_tautologies:                   0
% 3.50/0.99  inst_num_prop_implied:                  0
% 3.50/0.99  inst_num_existing_simplified:           0
% 3.50/0.99  inst_num_eq_res_simplified:             0
% 3.50/0.99  inst_num_child_elim:                    0
% 3.50/0.99  inst_num_of_dismatching_blockings:      742
% 3.50/0.99  inst_num_of_non_proper_insts:           1653
% 3.50/0.99  inst_num_of_duplicates:                 0
% 3.50/0.99  inst_inst_num_from_inst_to_res:         0
% 3.50/0.99  inst_dismatching_checking_time:         0.
% 3.50/0.99  
% 3.50/0.99  ------ Resolution
% 3.50/0.99  
% 3.50/0.99  res_num_of_clauses:                     0
% 3.50/0.99  res_num_in_passive:                     0
% 3.50/0.99  res_num_in_active:                      0
% 3.50/0.99  res_num_of_loops:                       102
% 3.50/0.99  res_forward_subset_subsumed:            58
% 3.50/0.99  res_backward_subset_subsumed:           4
% 3.50/0.99  res_forward_subsumed:                   0
% 3.50/0.99  res_backward_subsumed:                  0
% 3.50/0.99  res_forward_subsumption_resolution:     0
% 3.50/0.99  res_backward_subsumption_resolution:    0
% 3.50/0.99  res_clause_to_clause_subsumption:       592
% 3.50/0.99  res_orphan_elimination:                 0
% 3.50/0.99  res_tautology_del:                      181
% 3.50/0.99  res_num_eq_res_simplified:              0
% 3.50/0.99  res_num_sel_changes:                    0
% 3.50/0.99  res_moves_from_active_to_pass:          0
% 3.50/0.99  
% 3.50/0.99  ------ Superposition
% 3.50/0.99  
% 3.50/0.99  sup_time_total:                         0.
% 3.50/0.99  sup_time_generating:                    0.
% 3.50/0.99  sup_time_sim_full:                      0.
% 3.50/0.99  sup_time_sim_immed:                     0.
% 3.50/0.99  
% 3.50/0.99  sup_num_of_clauses:                     177
% 3.50/0.99  sup_num_in_active:                      100
% 3.50/0.99  sup_num_in_passive:                     77
% 3.50/0.99  sup_num_of_loops:                       125
% 3.50/0.99  sup_fw_superposition:                   142
% 3.50/0.99  sup_bw_superposition:                   149
% 3.50/0.99  sup_immediate_simplified:               69
% 3.50/0.99  sup_given_eliminated:                   0
% 3.50/0.99  comparisons_done:                       0
% 3.50/0.99  comparisons_avoided:                    3
% 3.50/0.99  
% 3.50/0.99  ------ Simplifications
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  sim_fw_subset_subsumed:                 5
% 3.50/0.99  sim_bw_subset_subsumed:                 9
% 3.50/0.99  sim_fw_subsumed:                        41
% 3.50/0.99  sim_bw_subsumed:                        1
% 3.50/0.99  sim_fw_subsumption_res:                 0
% 3.50/0.99  sim_bw_subsumption_res:                 0
% 3.50/0.99  sim_tautology_del:                      0
% 3.50/0.99  sim_eq_tautology_del:                   3
% 3.50/0.99  sim_eq_res_simp:                        1
% 3.50/0.99  sim_fw_demodulated:                     15
% 3.50/0.99  sim_bw_demodulated:                     22
% 3.50/0.99  sim_light_normalised:                   7
% 3.50/0.99  sim_joinable_taut:                      0
% 3.50/0.99  sim_joinable_simp:                      0
% 3.50/0.99  sim_ac_normalised:                      0
% 3.50/0.99  sim_smt_subsumption:                    0
% 3.50/0.99  
%------------------------------------------------------------------------------
