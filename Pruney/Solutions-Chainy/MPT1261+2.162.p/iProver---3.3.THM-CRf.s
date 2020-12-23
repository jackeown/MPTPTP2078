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
% DateTime   : Thu Dec  3 12:14:47 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 550 expanded)
%              Number of clauses        :   60 ( 158 expanded)
%              Number of leaves         :   15 ( 122 expanded)
%              Depth                    :   18
%              Number of atoms          :  313 (2401 expanded)
%              Number of equality atoms :  141 ( 792 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1)
          | ~ v4_pre_topc(sK1,X0) )
        & ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1)
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
              | ~ v4_pre_topc(X1,X0) )
            & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1)
            | ~ v4_pre_topc(X1,sK0) )
          & ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_774,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_782,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1251,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_774,c_782])).

cnf(c_15,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_775,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1422,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1251,c_775])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_780,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2274,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_780])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2530,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2274,c_20])).

cnf(c_2531,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2530])).

cnf(c_2536,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1422,c_2531])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_785,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_784,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1404,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_784])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_786,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_788,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1269,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_788])).

cnf(c_2040,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_1269])).

cnf(c_4009,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_785,c_2040])).

cnf(c_4116,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2536,c_4009])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_779,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_783,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1912,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k5_xboole_0(X1,k4_xboole_0(k2_tops_1(X0,X2),X1))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_779,c_783])).

cnf(c_3981,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_1912])).

cnf(c_4346,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3981,c_20])).

cnf(c_4347,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4346])).

cnf(c_4355,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_774,c_4347])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_777,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2055,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_777])).

cnf(c_982,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2526,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2055,c_17,c_16,c_982])).

cnf(c_4357,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_4355,c_2526])).

cnf(c_7816,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_4116,c_4357])).

cnf(c_1787,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_785,c_1269])).

cnf(c_1799,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1787,c_3])).

cnf(c_7819,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_7816,c_1799])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_778,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2298,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_778])).

cnf(c_990,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2702,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2298,c_17,c_16,c_990])).

cnf(c_8107,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_7819,c_2702])).

cnf(c_9,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_979,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_14,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8107,c_7819,c_979,c_14,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:22:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.62/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.98  
% 3.62/0.98  ------  iProver source info
% 3.62/0.98  
% 3.62/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.98  git: non_committed_changes: false
% 3.62/0.98  git: last_make_outside_of_git: false
% 3.62/0.98  
% 3.62/0.98  ------ 
% 3.62/0.98  ------ Parsing...
% 3.62/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.98  ------ Proving...
% 3.62/0.98  ------ Problem Properties 
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  clauses                                 18
% 3.62/0.98  conjectures                             5
% 3.62/0.98  EPR                                     5
% 3.62/0.98  Horn                                    17
% 3.62/0.98  unary                                   7
% 3.62/0.98  binary                                  4
% 3.62/0.98  lits                                    39
% 3.62/0.98  lits eq                                 10
% 3.62/0.98  fd_pure                                 0
% 3.62/0.98  fd_pseudo                               0
% 3.62/0.98  fd_cond                                 0
% 3.62/0.98  fd_pseudo_cond                          1
% 3.62/0.98  AC symbols                              0
% 3.62/0.98  
% 3.62/0.98  ------ Input Options Time Limit: Unbounded
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ 
% 3.62/0.98  Current options:
% 3.62/0.98  ------ 
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ Proving...
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  % SZS status Theorem for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  fof(f13,conjecture,(
% 3.62/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f14,negated_conjecture,(
% 3.62/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.62/0.98    inference(negated_conjecture,[],[f13])).
% 3.62/0.98  
% 3.62/0.98  fof(f25,plain,(
% 3.62/0.98    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f14])).
% 3.62/0.98  
% 3.62/0.98  fof(f26,plain,(
% 3.62/0.98    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.62/0.98    inference(flattening,[],[f25])).
% 3.62/0.98  
% 3.62/0.98  fof(f29,plain,(
% 3.62/0.98    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.62/0.98    inference(nnf_transformation,[],[f26])).
% 3.62/0.98  
% 3.62/0.98  fof(f30,plain,(
% 3.62/0.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.62/0.98    inference(flattening,[],[f29])).
% 3.62/0.98  
% 3.62/0.98  fof(f32,plain,(
% 3.62/0.98    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.62/0.98    introduced(choice_axiom,[])).
% 3.62/0.98  
% 3.62/0.98  fof(f31,plain,(
% 3.62/0.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.62/0.98    introduced(choice_axiom,[])).
% 3.62/0.98  
% 3.62/0.98  fof(f33,plain,(
% 3.62/0.98    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 3.62/0.98  
% 3.62/0.98  fof(f51,plain,(
% 3.62/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.62/0.98    inference(cnf_transformation,[],[f33])).
% 3.62/0.98  
% 3.62/0.98  fof(f8,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f18,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f8])).
% 3.62/0.98  
% 3.62/0.98  fof(f43,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f18])).
% 3.62/0.98  
% 3.62/0.98  fof(f52,plain,(
% 3.62/0.98    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.62/0.98    inference(cnf_transformation,[],[f33])).
% 3.62/0.98  
% 3.62/0.98  fof(f9,axiom,(
% 3.62/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f19,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(ennf_transformation,[],[f9])).
% 3.62/0.98  
% 3.62/0.98  fof(f20,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(flattening,[],[f19])).
% 3.62/0.98  
% 3.62/0.98  fof(f44,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f20])).
% 3.62/0.98  
% 3.62/0.98  fof(f50,plain,(
% 3.62/0.98    l1_pre_topc(sK0)),
% 3.62/0.98    inference(cnf_transformation,[],[f33])).
% 3.62/0.98  
% 3.62/0.98  fof(f4,axiom,(
% 3.62/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f39,plain,(
% 3.62/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f4])).
% 3.62/0.98  
% 3.62/0.98  fof(f2,axiom,(
% 3.62/0.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f37,plain,(
% 3.62/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.62/0.98    inference(cnf_transformation,[],[f2])).
% 3.62/0.98  
% 3.62/0.98  fof(f6,axiom,(
% 3.62/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f41,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f6])).
% 3.62/0.98  
% 3.62/0.98  fof(f54,plain,(
% 3.62/0.98    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 3.62/0.98    inference(definition_unfolding,[],[f37,f41])).
% 3.62/0.98  
% 3.62/0.98  fof(f5,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f15,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.62/0.98    inference(ennf_transformation,[],[f5])).
% 3.62/0.98  
% 3.62/0.98  fof(f40,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f15])).
% 3.62/0.98  
% 3.62/0.98  fof(f55,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 3.62/0.98    inference(definition_unfolding,[],[f40,f41])).
% 3.62/0.98  
% 3.62/0.98  fof(f3,axiom,(
% 3.62/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f38,plain,(
% 3.62/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f3])).
% 3.62/0.98  
% 3.62/0.98  fof(f1,axiom,(
% 3.62/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f27,plain,(
% 3.62/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.62/0.98    inference(nnf_transformation,[],[f1])).
% 3.62/0.98  
% 3.62/0.98  fof(f28,plain,(
% 3.62/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.62/0.98    inference(flattening,[],[f27])).
% 3.62/0.98  
% 3.62/0.98  fof(f36,plain,(
% 3.62/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f28])).
% 3.62/0.98  
% 3.62/0.98  fof(f10,axiom,(
% 3.62/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f21,plain,(
% 3.62/0.98    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f10])).
% 3.62/0.98  
% 3.62/0.98  fof(f22,plain,(
% 3.62/0.98    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(flattening,[],[f21])).
% 3.62/0.98  
% 3.62/0.98  fof(f46,plain,(
% 3.62/0.98    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f22])).
% 3.62/0.98  
% 3.62/0.98  fof(f7,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f16,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.62/0.98    inference(ennf_transformation,[],[f7])).
% 3.62/0.98  
% 3.62/0.98  fof(f17,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/0.98    inference(flattening,[],[f16])).
% 3.62/0.98  
% 3.62/0.98  fof(f42,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f17])).
% 3.62/0.98  
% 3.62/0.98  fof(f56,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/0.98    inference(definition_unfolding,[],[f42,f41])).
% 3.62/0.98  
% 3.62/0.98  fof(f12,axiom,(
% 3.62/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f24,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(ennf_transformation,[],[f12])).
% 3.62/0.98  
% 3.62/0.98  fof(f48,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f24])).
% 3.62/0.98  
% 3.62/0.98  fof(f11,axiom,(
% 3.62/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f23,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(ennf_transformation,[],[f11])).
% 3.62/0.98  
% 3.62/0.98  fof(f47,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f23])).
% 3.62/0.98  
% 3.62/0.98  fof(f45,plain,(
% 3.62/0.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f20])).
% 3.62/0.98  
% 3.62/0.98  fof(f53,plain,(
% 3.62/0.98    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.62/0.98    inference(cnf_transformation,[],[f33])).
% 3.62/0.98  
% 3.62/0.98  fof(f49,plain,(
% 3.62/0.98    v2_pre_topc(sK0)),
% 3.62/0.98    inference(cnf_transformation,[],[f33])).
% 3.62/0.98  
% 3.62/0.98  cnf(c_16,negated_conjecture,
% 3.62/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.62/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_774,plain,
% 3.62/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_8,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/0.98      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_782,plain,
% 3.62/0.98      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1251,plain,
% 3.62/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_774,c_782]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_15,negated_conjecture,
% 3.62/0.98      ( v4_pre_topc(sK1,sK0)
% 3.62/0.98      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_775,plain,
% 3.62/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.62/0.98      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1422,plain,
% 3.62/0.98      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.62/0.98      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.62/0.98      inference(demodulation,[status(thm)],[c_1251,c_775]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_10,plain,
% 3.62/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ l1_pre_topc(X1)
% 3.62/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 3.62/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_780,plain,
% 3.62/0.98      ( k2_pre_topc(X0,X1) = X1
% 3.62/0.98      | v4_pre_topc(X1,X0) != iProver_top
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.62/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2274,plain,
% 3.62/0.98      ( k2_pre_topc(sK0,sK1) = sK1
% 3.62/0.98      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.62/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_774,c_780]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_17,negated_conjecture,
% 3.62/0.98      ( l1_pre_topc(sK0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_20,plain,
% 3.62/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2530,plain,
% 3.62/0.98      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.62/0.98      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_2274,c_20]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2531,plain,
% 3.62/0.98      ( k2_pre_topc(sK0,sK1) = sK1
% 3.62/0.98      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.62/0.98      inference(renaming,[status(thm)],[c_2530]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2536,plain,
% 3.62/0.98      ( k2_pre_topc(sK0,sK1) = sK1
% 3.62/0.98      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_1422,c_2531]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5,plain,
% 3.62/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_785,plain,
% 3.62/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3,plain,
% 3.62/0.98      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 3.62/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
% 3.62/0.98      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_784,plain,
% 3.62/0.98      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) != iProver_top
% 3.62/0.98      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1404,plain,
% 3.62/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.62/0.98      | r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3,c_784]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4,plain,
% 3.62/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_786,plain,
% 3.62/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_0,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.62/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_788,plain,
% 3.62/0.98      ( X0 = X1
% 3.62/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.62/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1269,plain,
% 3.62/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_786,c_788]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2040,plain,
% 3.62/0.98      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.62/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_1404,c_1269]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4009,plain,
% 3.62/0.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_785,c_2040]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4116,plain,
% 3.62/0.98      ( k2_pre_topc(sK0,sK1) = sK1
% 3.62/0.98      | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_2536,c_4009]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_11,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ l1_pre_topc(X1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_779,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.62/0.98      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.62/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.62/0.98      | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_783,plain,
% 3.62/0.98      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1912,plain,
% 3.62/0.98      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k5_xboole_0(X1,k4_xboole_0(k2_tops_1(X0,X2),X1))
% 3.62/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.62/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_779,c_783]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3981,plain,
% 3.62/0.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.62/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_774,c_1912]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4346,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.62/0.98      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1)) ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_3981,c_20]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4347,plain,
% 3.62/0.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.62/0.98      inference(renaming,[status(thm)],[c_4346]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4355,plain,
% 3.62/0.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_774,c_4347]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_13,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ l1_pre_topc(X1)
% 3.62/0.98      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_777,plain,
% 3.62/0.98      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.62/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2055,plain,
% 3.62/0.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.62/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_774,c_777]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_982,plain,
% 3.62/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.62/0.98      | ~ l1_pre_topc(sK0)
% 3.62/0.98      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2526,plain,
% 3.62/0.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_2055,c_17,c_16,c_982]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4357,plain,
% 3.62/0.98      ( k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.62/0.98      inference(light_normalisation,[status(thm)],[c_4355,c_2526]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7816,plain,
% 3.62/0.98      ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
% 3.62/0.98      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_4116,c_4357]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1787,plain,
% 3.62/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_785,c_1269]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1799,plain,
% 3.62/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.62/0.98      inference(demodulation,[status(thm)],[c_1787,c_3]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7819,plain,
% 3.62/0.98      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.62/0.98      inference(demodulation,[status(thm)],[c_7816,c_1799]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_12,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ l1_pre_topc(X1)
% 3.62/0.98      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_778,plain,
% 3.62/0.98      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.62/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2298,plain,
% 3.62/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.62/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_774,c_778]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_990,plain,
% 3.62/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.62/0.98      | ~ l1_pre_topc(sK0)
% 3.62/0.98      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2702,plain,
% 3.62/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_2298,c_17,c_16,c_990]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_8107,plain,
% 3.62/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.62/0.98      inference(demodulation,[status(thm)],[c_7819,c_2702]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_9,plain,
% 3.62/0.98      ( v4_pre_topc(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ l1_pre_topc(X1)
% 3.62/0.98      | ~ v2_pre_topc(X1)
% 3.62/0.98      | k2_pre_topc(X1,X0) != X0 ),
% 3.62/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_979,plain,
% 3.62/0.98      ( v4_pre_topc(sK1,sK0)
% 3.62/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.62/0.98      | ~ l1_pre_topc(sK0)
% 3.62/0.98      | ~ v2_pre_topc(sK0)
% 3.62/0.98      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_14,negated_conjecture,
% 3.62/0.98      ( ~ v4_pre_topc(sK1,sK0)
% 3.62/0.98      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_18,negated_conjecture,
% 3.62/0.98      ( v2_pre_topc(sK0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(contradiction,plain,
% 3.62/0.98      ( $false ),
% 3.62/0.98      inference(minisat,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_8107,c_7819,c_979,c_14,c_16,c_17,c_18]) ).
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  ------                               Statistics
% 3.62/0.98  
% 3.62/0.98  ------ Selected
% 3.62/0.98  
% 3.62/0.98  total_time:                             0.273
% 3.62/0.98  
%------------------------------------------------------------------------------
