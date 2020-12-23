%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:29 EST 2020

% Result     : Theorem 1.14s
% Output     : CNFRefutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 555 expanded)
%              Number of clauses        :   63 ( 136 expanded)
%              Number of leaves         :   13 ( 124 expanded)
%              Depth                    :   17
%              Number of atoms          :  379 (2978 expanded)
%              Number of equality atoms :  121 ( 820 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k2_tops_1(X0,sK1) != sK1
          | ~ v3_tops_1(sK1,X0) )
        & ( k2_tops_1(X0,sK1) = sK1
          | v3_tops_1(sK1,X0) )
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( k2_tops_1(sK0,sK1) != sK1
      | ~ v3_tops_1(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = sK1
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
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

fof(f12,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_8,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_310,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_311,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_313,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_545,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_16,c_313])).

cnf(c_953,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_52,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_56,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_295,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_296,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_405,plain,
    ( v2_tops_1(X0,sK0)
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_296])).

cnf(c_406,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_395,plain,
    ( ~ v2_tops_1(X0,sK0)
    | k1_tops_1(sK0,X0) = k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_311])).

cnf(c_396,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_441,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_406,c_396])).

cnf(c_11,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,negated_conjecture,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_130,plain,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_260,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(sK0,sK1) = sK1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_130])).

cnf(c_261,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_263,plain,
    ( v2_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_261,c_17,c_16])).

cnf(c_485,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_263,c_396])).

cnf(c_674,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1041,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_1043,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | k2_tops_1(sK0,sK1) != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_1101,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_953,c_52,c_56,c_441,c_485,c_1043])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_380,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_341])).

cnf(c_381,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_5,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_237,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_239,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_237,c_17,c_16])).

cnf(c_977,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_381,c_239])).

cnf(c_1105,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1101,c_977])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_371,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_372,plain,
    ( k7_subset_1(X0,sK1,X1) = k4_xboole_0(sK1,X1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1023,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(equality_resolution,[status(thm)],[c_372])).

cnf(c_1107,plain,
    ( k2_tops_1(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_1105,c_3,c_1023])).

cnf(c_7,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_325,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_326,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_385,plain,
    ( v2_tops_1(X0,sK0)
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_326])).

cnf(c_386,plain,
    ( v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_12,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_222,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_223,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_225,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_17,c_16])).

cnf(c_13,negated_conjecture,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_128,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_248,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(resolution,[status(thm)],[c_225,c_128])).

cnf(c_469,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_386,c_248])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1107,c_1101,c_469])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.14/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.14/1.00  
% 1.14/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.14/1.00  
% 1.14/1.00  ------  iProver source info
% 1.14/1.00  
% 1.14/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.14/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.14/1.00  git: non_committed_changes: false
% 1.14/1.00  git: last_make_outside_of_git: false
% 1.14/1.00  
% 1.14/1.00  ------ 
% 1.14/1.00  
% 1.14/1.00  ------ Input Options
% 1.14/1.00  
% 1.14/1.00  --out_options                           all
% 1.14/1.00  --tptp_safe_out                         true
% 1.14/1.00  --problem_path                          ""
% 1.14/1.00  --include_path                          ""
% 1.14/1.00  --clausifier                            res/vclausify_rel
% 1.14/1.00  --clausifier_options                    --mode clausify
% 1.14/1.00  --stdin                                 false
% 1.14/1.00  --stats_out                             all
% 1.14/1.00  
% 1.14/1.00  ------ General Options
% 1.14/1.00  
% 1.14/1.00  --fof                                   false
% 1.14/1.00  --time_out_real                         305.
% 1.14/1.00  --time_out_virtual                      -1.
% 1.14/1.00  --symbol_type_check                     false
% 1.14/1.00  --clausify_out                          false
% 1.14/1.00  --sig_cnt_out                           false
% 1.14/1.00  --trig_cnt_out                          false
% 1.14/1.00  --trig_cnt_out_tolerance                1.
% 1.14/1.00  --trig_cnt_out_sk_spl                   false
% 1.14/1.00  --abstr_cl_out                          false
% 1.14/1.00  
% 1.14/1.00  ------ Global Options
% 1.14/1.00  
% 1.14/1.00  --schedule                              default
% 1.14/1.00  --add_important_lit                     false
% 1.14/1.00  --prop_solver_per_cl                    1000
% 1.14/1.00  --min_unsat_core                        false
% 1.14/1.00  --soft_assumptions                      false
% 1.14/1.00  --soft_lemma_size                       3
% 1.14/1.00  --prop_impl_unit_size                   0
% 1.14/1.00  --prop_impl_unit                        []
% 1.14/1.00  --share_sel_clauses                     true
% 1.14/1.00  --reset_solvers                         false
% 1.14/1.00  --bc_imp_inh                            [conj_cone]
% 1.14/1.00  --conj_cone_tolerance                   3.
% 1.14/1.00  --extra_neg_conj                        none
% 1.14/1.00  --large_theory_mode                     true
% 1.14/1.00  --prolific_symb_bound                   200
% 1.14/1.00  --lt_threshold                          2000
% 1.14/1.00  --clause_weak_htbl                      true
% 1.14/1.00  --gc_record_bc_elim                     false
% 1.14/1.00  
% 1.14/1.00  ------ Preprocessing Options
% 1.14/1.00  
% 1.14/1.00  --preprocessing_flag                    true
% 1.14/1.00  --time_out_prep_mult                    0.1
% 1.14/1.00  --splitting_mode                        input
% 1.14/1.00  --splitting_grd                         true
% 1.14/1.00  --splitting_cvd                         false
% 1.14/1.00  --splitting_cvd_svl                     false
% 1.14/1.00  --splitting_nvd                         32
% 1.14/1.00  --sub_typing                            true
% 1.14/1.00  --prep_gs_sim                           true
% 1.14/1.00  --prep_unflatten                        true
% 1.14/1.00  --prep_res_sim                          true
% 1.14/1.00  --prep_upred                            true
% 1.14/1.00  --prep_sem_filter                       exhaustive
% 1.14/1.00  --prep_sem_filter_out                   false
% 1.14/1.00  --pred_elim                             true
% 1.14/1.00  --res_sim_input                         true
% 1.14/1.00  --eq_ax_congr_red                       true
% 1.14/1.00  --pure_diseq_elim                       true
% 1.14/1.00  --brand_transform                       false
% 1.14/1.00  --non_eq_to_eq                          false
% 1.14/1.00  --prep_def_merge                        true
% 1.14/1.00  --prep_def_merge_prop_impl              false
% 1.14/1.00  --prep_def_merge_mbd                    true
% 1.14/1.00  --prep_def_merge_tr_red                 false
% 1.14/1.00  --prep_def_merge_tr_cl                  false
% 1.14/1.00  --smt_preprocessing                     true
% 1.14/1.00  --smt_ac_axioms                         fast
% 1.14/1.00  --preprocessed_out                      false
% 1.14/1.00  --preprocessed_stats                    false
% 1.14/1.00  
% 1.14/1.00  ------ Abstraction refinement Options
% 1.14/1.00  
% 1.14/1.00  --abstr_ref                             []
% 1.14/1.00  --abstr_ref_prep                        false
% 1.14/1.00  --abstr_ref_until_sat                   false
% 1.14/1.00  --abstr_ref_sig_restrict                funpre
% 1.14/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.14/1.00  --abstr_ref_under                       []
% 1.14/1.00  
% 1.14/1.00  ------ SAT Options
% 1.14/1.00  
% 1.14/1.00  --sat_mode                              false
% 1.14/1.00  --sat_fm_restart_options                ""
% 1.14/1.00  --sat_gr_def                            false
% 1.14/1.00  --sat_epr_types                         true
% 1.14/1.00  --sat_non_cyclic_types                  false
% 1.14/1.00  --sat_finite_models                     false
% 1.14/1.00  --sat_fm_lemmas                         false
% 1.14/1.00  --sat_fm_prep                           false
% 1.14/1.00  --sat_fm_uc_incr                        true
% 1.14/1.00  --sat_out_model                         small
% 1.14/1.00  --sat_out_clauses                       false
% 1.14/1.00  
% 1.14/1.00  ------ QBF Options
% 1.14/1.00  
% 1.14/1.00  --qbf_mode                              false
% 1.14/1.00  --qbf_elim_univ                         false
% 1.14/1.00  --qbf_dom_inst                          none
% 1.14/1.00  --qbf_dom_pre_inst                      false
% 1.14/1.00  --qbf_sk_in                             false
% 1.14/1.00  --qbf_pred_elim                         true
% 1.14/1.00  --qbf_split                             512
% 1.14/1.00  
% 1.14/1.00  ------ BMC1 Options
% 1.14/1.00  
% 1.14/1.00  --bmc1_incremental                      false
% 1.14/1.00  --bmc1_axioms                           reachable_all
% 1.14/1.00  --bmc1_min_bound                        0
% 1.14/1.00  --bmc1_max_bound                        -1
% 1.14/1.00  --bmc1_max_bound_default                -1
% 1.14/1.00  --bmc1_symbol_reachability              true
% 1.14/1.00  --bmc1_property_lemmas                  false
% 1.14/1.00  --bmc1_k_induction                      false
% 1.14/1.00  --bmc1_non_equiv_states                 false
% 1.14/1.00  --bmc1_deadlock                         false
% 1.14/1.00  --bmc1_ucm                              false
% 1.14/1.00  --bmc1_add_unsat_core                   none
% 1.14/1.00  --bmc1_unsat_core_children              false
% 1.14/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.14/1.00  --bmc1_out_stat                         full
% 1.14/1.00  --bmc1_ground_init                      false
% 1.14/1.00  --bmc1_pre_inst_next_state              false
% 1.14/1.00  --bmc1_pre_inst_state                   false
% 1.14/1.00  --bmc1_pre_inst_reach_state             false
% 1.14/1.00  --bmc1_out_unsat_core                   false
% 1.14/1.00  --bmc1_aig_witness_out                  false
% 1.14/1.00  --bmc1_verbose                          false
% 1.14/1.00  --bmc1_dump_clauses_tptp                false
% 1.14/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.14/1.00  --bmc1_dump_file                        -
% 1.14/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.14/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.14/1.00  --bmc1_ucm_extend_mode                  1
% 1.14/1.00  --bmc1_ucm_init_mode                    2
% 1.14/1.00  --bmc1_ucm_cone_mode                    none
% 1.14/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.14/1.00  --bmc1_ucm_relax_model                  4
% 1.14/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.14/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.14/1.00  --bmc1_ucm_layered_model                none
% 1.14/1.00  --bmc1_ucm_max_lemma_size               10
% 1.14/1.00  
% 1.14/1.00  ------ AIG Options
% 1.14/1.00  
% 1.14/1.00  --aig_mode                              false
% 1.14/1.00  
% 1.14/1.00  ------ Instantiation Options
% 1.14/1.00  
% 1.14/1.00  --instantiation_flag                    true
% 1.14/1.00  --inst_sos_flag                         false
% 1.14/1.00  --inst_sos_phase                        true
% 1.14/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.14/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.14/1.00  --inst_lit_sel_side                     num_symb
% 1.14/1.00  --inst_solver_per_active                1400
% 1.14/1.00  --inst_solver_calls_frac                1.
% 1.14/1.00  --inst_passive_queue_type               priority_queues
% 1.14/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.14/1.00  --inst_passive_queues_freq              [25;2]
% 1.14/1.00  --inst_dismatching                      true
% 1.14/1.00  --inst_eager_unprocessed_to_passive     true
% 1.14/1.00  --inst_prop_sim_given                   true
% 1.14/1.00  --inst_prop_sim_new                     false
% 1.14/1.00  --inst_subs_new                         false
% 1.14/1.00  --inst_eq_res_simp                      false
% 1.14/1.00  --inst_subs_given                       false
% 1.14/1.00  --inst_orphan_elimination               true
% 1.14/1.00  --inst_learning_loop_flag               true
% 1.14/1.00  --inst_learning_start                   3000
% 1.14/1.00  --inst_learning_factor                  2
% 1.14/1.00  --inst_start_prop_sim_after_learn       3
% 1.14/1.00  --inst_sel_renew                        solver
% 1.14/1.00  --inst_lit_activity_flag                true
% 1.14/1.00  --inst_restr_to_given                   false
% 1.14/1.00  --inst_activity_threshold               500
% 1.14/1.00  --inst_out_proof                        true
% 1.14/1.00  
% 1.14/1.00  ------ Resolution Options
% 1.14/1.00  
% 1.14/1.00  --resolution_flag                       true
% 1.14/1.00  --res_lit_sel                           adaptive
% 1.14/1.00  --res_lit_sel_side                      none
% 1.14/1.00  --res_ordering                          kbo
% 1.14/1.00  --res_to_prop_solver                    active
% 1.14/1.00  --res_prop_simpl_new                    false
% 1.14/1.00  --res_prop_simpl_given                  true
% 1.14/1.00  --res_passive_queue_type                priority_queues
% 1.14/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.14/1.00  --res_passive_queues_freq               [15;5]
% 1.14/1.00  --res_forward_subs                      full
% 1.14/1.00  --res_backward_subs                     full
% 1.14/1.00  --res_forward_subs_resolution           true
% 1.14/1.00  --res_backward_subs_resolution          true
% 1.14/1.00  --res_orphan_elimination                true
% 1.14/1.00  --res_time_limit                        2.
% 1.14/1.00  --res_out_proof                         true
% 1.14/1.00  
% 1.14/1.00  ------ Superposition Options
% 1.14/1.00  
% 1.14/1.00  --superposition_flag                    true
% 1.14/1.00  --sup_passive_queue_type                priority_queues
% 1.14/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.14/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.14/1.00  --demod_completeness_check              fast
% 1.14/1.00  --demod_use_ground                      true
% 1.14/1.00  --sup_to_prop_solver                    passive
% 1.14/1.00  --sup_prop_simpl_new                    true
% 1.14/1.00  --sup_prop_simpl_given                  true
% 1.14/1.00  --sup_fun_splitting                     false
% 1.14/1.00  --sup_smt_interval                      50000
% 1.14/1.00  
% 1.14/1.00  ------ Superposition Simplification Setup
% 1.14/1.00  
% 1.14/1.00  --sup_indices_passive                   []
% 1.14/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.14/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.00  --sup_full_bw                           [BwDemod]
% 1.14/1.00  --sup_immed_triv                        [TrivRules]
% 1.14/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.14/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.00  --sup_immed_bw_main                     []
% 1.14/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.14/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.00  
% 1.14/1.00  ------ Combination Options
% 1.14/1.00  
% 1.14/1.00  --comb_res_mult                         3
% 1.14/1.00  --comb_sup_mult                         2
% 1.14/1.00  --comb_inst_mult                        10
% 1.14/1.00  
% 1.14/1.00  ------ Debug Options
% 1.14/1.00  
% 1.14/1.00  --dbg_backtrace                         false
% 1.14/1.00  --dbg_dump_prop_clauses                 false
% 1.14/1.00  --dbg_dump_prop_clauses_file            -
% 1.14/1.00  --dbg_out_stat                          false
% 1.14/1.00  ------ Parsing...
% 1.14/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.14/1.00  
% 1.14/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.14/1.00  
% 1.14/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.14/1.00  
% 1.14/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.14/1.00  ------ Proving...
% 1.14/1.00  ------ Problem Properties 
% 1.14/1.00  
% 1.14/1.00  
% 1.14/1.00  clauses                                 12
% 1.14/1.00  conjectures                             0
% 1.14/1.00  EPR                                     2
% 1.14/1.00  Horn                                    11
% 1.14/1.00  unary                                   4
% 1.14/1.00  binary                                  7
% 1.14/1.00  lits                                    21
% 1.14/1.00  lits eq                                 10
% 1.14/1.00  fd_pure                                 0
% 1.14/1.00  fd_pseudo                               0
% 1.14/1.00  fd_cond                                 0
% 1.14/1.00  fd_pseudo_cond                          1
% 1.14/1.00  AC symbols                              0
% 1.14/1.00  
% 1.14/1.00  ------ Schedule dynamic 5 is on 
% 1.14/1.00  
% 1.14/1.00  ------ no conjectures: strip conj schedule 
% 1.14/1.00  
% 1.14/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.14/1.00  
% 1.14/1.00  
% 1.14/1.00  ------ 
% 1.14/1.00  Current options:
% 1.14/1.00  ------ 
% 1.14/1.00  
% 1.14/1.00  ------ Input Options
% 1.14/1.00  
% 1.14/1.00  --out_options                           all
% 1.14/1.00  --tptp_safe_out                         true
% 1.14/1.00  --problem_path                          ""
% 1.14/1.00  --include_path                          ""
% 1.14/1.00  --clausifier                            res/vclausify_rel
% 1.14/1.00  --clausifier_options                    --mode clausify
% 1.14/1.00  --stdin                                 false
% 1.14/1.00  --stats_out                             all
% 1.14/1.00  
% 1.14/1.00  ------ General Options
% 1.14/1.00  
% 1.14/1.00  --fof                                   false
% 1.14/1.00  --time_out_real                         305.
% 1.14/1.00  --time_out_virtual                      -1.
% 1.14/1.00  --symbol_type_check                     false
% 1.14/1.00  --clausify_out                          false
% 1.14/1.00  --sig_cnt_out                           false
% 1.14/1.00  --trig_cnt_out                          false
% 1.14/1.00  --trig_cnt_out_tolerance                1.
% 1.14/1.00  --trig_cnt_out_sk_spl                   false
% 1.14/1.00  --abstr_cl_out                          false
% 1.14/1.00  
% 1.14/1.00  ------ Global Options
% 1.14/1.00  
% 1.14/1.00  --schedule                              default
% 1.14/1.00  --add_important_lit                     false
% 1.14/1.00  --prop_solver_per_cl                    1000
% 1.14/1.00  --min_unsat_core                        false
% 1.14/1.00  --soft_assumptions                      false
% 1.14/1.00  --soft_lemma_size                       3
% 1.14/1.00  --prop_impl_unit_size                   0
% 1.14/1.00  --prop_impl_unit                        []
% 1.14/1.00  --share_sel_clauses                     true
% 1.14/1.00  --reset_solvers                         false
% 1.14/1.00  --bc_imp_inh                            [conj_cone]
% 1.14/1.00  --conj_cone_tolerance                   3.
% 1.14/1.00  --extra_neg_conj                        none
% 1.14/1.00  --large_theory_mode                     true
% 1.14/1.00  --prolific_symb_bound                   200
% 1.14/1.00  --lt_threshold                          2000
% 1.14/1.00  --clause_weak_htbl                      true
% 1.14/1.00  --gc_record_bc_elim                     false
% 1.14/1.00  
% 1.14/1.00  ------ Preprocessing Options
% 1.14/1.00  
% 1.14/1.00  --preprocessing_flag                    true
% 1.14/1.00  --time_out_prep_mult                    0.1
% 1.14/1.00  --splitting_mode                        input
% 1.14/1.00  --splitting_grd                         true
% 1.14/1.00  --splitting_cvd                         false
% 1.14/1.00  --splitting_cvd_svl                     false
% 1.14/1.00  --splitting_nvd                         32
% 1.14/1.00  --sub_typing                            true
% 1.14/1.00  --prep_gs_sim                           true
% 1.14/1.00  --prep_unflatten                        true
% 1.14/1.00  --prep_res_sim                          true
% 1.14/1.00  --prep_upred                            true
% 1.14/1.00  --prep_sem_filter                       exhaustive
% 1.14/1.00  --prep_sem_filter_out                   false
% 1.14/1.00  --pred_elim                             true
% 1.14/1.00  --res_sim_input                         true
% 1.14/1.00  --eq_ax_congr_red                       true
% 1.14/1.00  --pure_diseq_elim                       true
% 1.14/1.00  --brand_transform                       false
% 1.14/1.00  --non_eq_to_eq                          false
% 1.14/1.00  --prep_def_merge                        true
% 1.14/1.00  --prep_def_merge_prop_impl              false
% 1.14/1.00  --prep_def_merge_mbd                    true
% 1.14/1.00  --prep_def_merge_tr_red                 false
% 1.14/1.00  --prep_def_merge_tr_cl                  false
% 1.14/1.00  --smt_preprocessing                     true
% 1.14/1.00  --smt_ac_axioms                         fast
% 1.14/1.00  --preprocessed_out                      false
% 1.14/1.00  --preprocessed_stats                    false
% 1.14/1.00  
% 1.14/1.00  ------ Abstraction refinement Options
% 1.14/1.00  
% 1.14/1.00  --abstr_ref                             []
% 1.14/1.00  --abstr_ref_prep                        false
% 1.14/1.00  --abstr_ref_until_sat                   false
% 1.14/1.00  --abstr_ref_sig_restrict                funpre
% 1.14/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.14/1.00  --abstr_ref_under                       []
% 1.14/1.00  
% 1.14/1.00  ------ SAT Options
% 1.14/1.00  
% 1.14/1.00  --sat_mode                              false
% 1.14/1.00  --sat_fm_restart_options                ""
% 1.14/1.00  --sat_gr_def                            false
% 1.14/1.00  --sat_epr_types                         true
% 1.14/1.00  --sat_non_cyclic_types                  false
% 1.14/1.00  --sat_finite_models                     false
% 1.14/1.00  --sat_fm_lemmas                         false
% 1.14/1.00  --sat_fm_prep                           false
% 1.14/1.00  --sat_fm_uc_incr                        true
% 1.14/1.00  --sat_out_model                         small
% 1.14/1.00  --sat_out_clauses                       false
% 1.14/1.00  
% 1.14/1.00  ------ QBF Options
% 1.14/1.00  
% 1.14/1.00  --qbf_mode                              false
% 1.14/1.00  --qbf_elim_univ                         false
% 1.14/1.00  --qbf_dom_inst                          none
% 1.14/1.00  --qbf_dom_pre_inst                      false
% 1.14/1.00  --qbf_sk_in                             false
% 1.14/1.00  --qbf_pred_elim                         true
% 1.14/1.00  --qbf_split                             512
% 1.14/1.00  
% 1.14/1.00  ------ BMC1 Options
% 1.14/1.00  
% 1.14/1.00  --bmc1_incremental                      false
% 1.14/1.00  --bmc1_axioms                           reachable_all
% 1.14/1.00  --bmc1_min_bound                        0
% 1.14/1.00  --bmc1_max_bound                        -1
% 1.14/1.00  --bmc1_max_bound_default                -1
% 1.14/1.00  --bmc1_symbol_reachability              true
% 1.14/1.00  --bmc1_property_lemmas                  false
% 1.14/1.00  --bmc1_k_induction                      false
% 1.14/1.00  --bmc1_non_equiv_states                 false
% 1.14/1.00  --bmc1_deadlock                         false
% 1.14/1.00  --bmc1_ucm                              false
% 1.14/1.00  --bmc1_add_unsat_core                   none
% 1.14/1.00  --bmc1_unsat_core_children              false
% 1.14/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.14/1.00  --bmc1_out_stat                         full
% 1.14/1.00  --bmc1_ground_init                      false
% 1.14/1.00  --bmc1_pre_inst_next_state              false
% 1.14/1.00  --bmc1_pre_inst_state                   false
% 1.14/1.00  --bmc1_pre_inst_reach_state             false
% 1.14/1.00  --bmc1_out_unsat_core                   false
% 1.14/1.00  --bmc1_aig_witness_out                  false
% 1.14/1.00  --bmc1_verbose                          false
% 1.14/1.00  --bmc1_dump_clauses_tptp                false
% 1.14/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.14/1.00  --bmc1_dump_file                        -
% 1.14/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.14/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.14/1.00  --bmc1_ucm_extend_mode                  1
% 1.14/1.00  --bmc1_ucm_init_mode                    2
% 1.14/1.00  --bmc1_ucm_cone_mode                    none
% 1.14/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.14/1.00  --bmc1_ucm_relax_model                  4
% 1.14/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.14/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.14/1.00  --bmc1_ucm_layered_model                none
% 1.14/1.00  --bmc1_ucm_max_lemma_size               10
% 1.14/1.00  
% 1.14/1.00  ------ AIG Options
% 1.14/1.00  
% 1.14/1.00  --aig_mode                              false
% 1.14/1.00  
% 1.14/1.00  ------ Instantiation Options
% 1.14/1.00  
% 1.14/1.00  --instantiation_flag                    true
% 1.14/1.00  --inst_sos_flag                         false
% 1.14/1.00  --inst_sos_phase                        true
% 1.14/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.14/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.14/1.00  --inst_lit_sel_side                     none
% 1.14/1.00  --inst_solver_per_active                1400
% 1.14/1.00  --inst_solver_calls_frac                1.
% 1.14/1.00  --inst_passive_queue_type               priority_queues
% 1.14/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.14/1.00  --inst_passive_queues_freq              [25;2]
% 1.14/1.00  --inst_dismatching                      true
% 1.14/1.00  --inst_eager_unprocessed_to_passive     true
% 1.14/1.00  --inst_prop_sim_given                   true
% 1.14/1.00  --inst_prop_sim_new                     false
% 1.14/1.00  --inst_subs_new                         false
% 1.14/1.00  --inst_eq_res_simp                      false
% 1.14/1.00  --inst_subs_given                       false
% 1.14/1.00  --inst_orphan_elimination               true
% 1.14/1.00  --inst_learning_loop_flag               true
% 1.14/1.00  --inst_learning_start                   3000
% 1.14/1.00  --inst_learning_factor                  2
% 1.14/1.00  --inst_start_prop_sim_after_learn       3
% 1.14/1.00  --inst_sel_renew                        solver
% 1.14/1.00  --inst_lit_activity_flag                true
% 1.14/1.00  --inst_restr_to_given                   false
% 1.14/1.00  --inst_activity_threshold               500
% 1.14/1.00  --inst_out_proof                        true
% 1.14/1.00  
% 1.14/1.00  ------ Resolution Options
% 1.14/1.00  
% 1.14/1.00  --resolution_flag                       false
% 1.14/1.00  --res_lit_sel                           adaptive
% 1.14/1.00  --res_lit_sel_side                      none
% 1.14/1.00  --res_ordering                          kbo
% 1.14/1.00  --res_to_prop_solver                    active
% 1.14/1.00  --res_prop_simpl_new                    false
% 1.14/1.00  --res_prop_simpl_given                  true
% 1.14/1.00  --res_passive_queue_type                priority_queues
% 1.14/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.14/1.00  --res_passive_queues_freq               [15;5]
% 1.14/1.00  --res_forward_subs                      full
% 1.14/1.00  --res_backward_subs                     full
% 1.14/1.00  --res_forward_subs_resolution           true
% 1.14/1.00  --res_backward_subs_resolution          true
% 1.14/1.00  --res_orphan_elimination                true
% 1.14/1.00  --res_time_limit                        2.
% 1.14/1.00  --res_out_proof                         true
% 1.14/1.00  
% 1.14/1.00  ------ Superposition Options
% 1.14/1.00  
% 1.14/1.00  --superposition_flag                    true
% 1.14/1.00  --sup_passive_queue_type                priority_queues
% 1.14/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.14/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.14/1.00  --demod_completeness_check              fast
% 1.14/1.00  --demod_use_ground                      true
% 1.14/1.00  --sup_to_prop_solver                    passive
% 1.14/1.00  --sup_prop_simpl_new                    true
% 1.14/1.00  --sup_prop_simpl_given                  true
% 1.14/1.00  --sup_fun_splitting                     false
% 1.14/1.00  --sup_smt_interval                      50000
% 1.14/1.00  
% 1.14/1.00  ------ Superposition Simplification Setup
% 1.14/1.00  
% 1.14/1.00  --sup_indices_passive                   []
% 1.14/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.14/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.00  --sup_full_bw                           [BwDemod]
% 1.14/1.00  --sup_immed_triv                        [TrivRules]
% 1.14/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.14/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.00  --sup_immed_bw_main                     []
% 1.14/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.14/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.00  
% 1.14/1.00  ------ Combination Options
% 1.14/1.00  
% 1.14/1.00  --comb_res_mult                         3
% 1.14/1.00  --comb_sup_mult                         2
% 1.14/1.00  --comb_inst_mult                        10
% 1.14/1.00  
% 1.14/1.00  ------ Debug Options
% 1.14/1.00  
% 1.14/1.00  --dbg_backtrace                         false
% 1.14/1.00  --dbg_dump_prop_clauses                 false
% 1.14/1.00  --dbg_dump_prop_clauses_file            -
% 1.14/1.00  --dbg_out_stat                          false
% 1.14/1.00  
% 1.14/1.00  
% 1.14/1.00  
% 1.14/1.00  
% 1.14/1.00  ------ Proving...
% 1.14/1.00  
% 1.14/1.00  
% 1.14/1.00  % SZS status Theorem for theBenchmark.p
% 1.14/1.00  
% 1.14/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.14/1.00  
% 1.14/1.00  fof(f10,conjecture,(
% 1.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.00  
% 1.14/1.00  fof(f11,negated_conjecture,(
% 1.14/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.14/1.00    inference(negated_conjecture,[],[f10])).
% 1.14/1.00  
% 1.14/1.00  fof(f23,plain,(
% 1.14/1.00    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.14/1.00    inference(ennf_transformation,[],[f11])).
% 1.14/1.00  
% 1.14/1.00  fof(f24,plain,(
% 1.14/1.00    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.14/1.00    inference(flattening,[],[f23])).
% 1.14/1.00  
% 1.14/1.00  fof(f29,plain,(
% 1.14/1.00    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.14/1.00    inference(nnf_transformation,[],[f24])).
% 1.14/1.00  
% 1.14/1.00  fof(f30,plain,(
% 1.14/1.00    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.14/1.00    inference(flattening,[],[f29])).
% 1.14/1.00  
% 1.14/1.00  fof(f32,plain,(
% 1.14/1.00    ( ! [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k2_tops_1(X0,sK1) != sK1 | ~v3_tops_1(sK1,X0)) & (k2_tops_1(X0,sK1) = sK1 | v3_tops_1(sK1,X0)) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.14/1.00    introduced(choice_axiom,[])).
% 1.14/1.00  
% 1.14/1.00  fof(f31,plain,(
% 1.14/1.00    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.14/1.00    introduced(choice_axiom,[])).
% 1.14/1.00  
% 1.14/1.00  fof(f33,plain,(
% 1.14/1.00    ((k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)) & (k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.14/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 1.14/1.00  
% 1.14/1.00  fof(f48,plain,(
% 1.14/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.14/1.00    inference(cnf_transformation,[],[f33])).
% 1.14/1.00  
% 1.14/1.00  fof(f6,axiom,(
% 1.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.00  
% 1.14/1.00  fof(f17,plain,(
% 1.14/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/1.00    inference(ennf_transformation,[],[f6])).
% 1.14/1.00  
% 1.14/1.00  fof(f27,plain,(
% 1.14/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/1.00    inference(nnf_transformation,[],[f17])).
% 1.14/1.00  
% 1.14/1.00  fof(f41,plain,(
% 1.14/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.14/1.00    inference(cnf_transformation,[],[f27])).
% 1.14/1.00  
% 1.14/1.00  fof(f47,plain,(
% 1.14/1.00    l1_pre_topc(sK0)),
% 1.14/1.00    inference(cnf_transformation,[],[f33])).
% 1.14/1.00  
% 1.14/1.00  fof(f1,axiom,(
% 1.14/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.00  
% 1.14/1.00  fof(f25,plain,(
% 1.14/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.14/1.00    inference(nnf_transformation,[],[f1])).
% 1.14/1.00  
% 1.14/1.00  fof(f26,plain,(
% 1.14/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.14/1.00    inference(flattening,[],[f25])).
% 1.14/1.00  
% 1.14/1.00  fof(f34,plain,(
% 1.14/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.14/1.00    inference(cnf_transformation,[],[f26])).
% 1.14/1.00  
% 1.14/1.00  fof(f53,plain,(
% 1.14/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.14/1.00    inference(equality_resolution,[],[f34])).
% 1.14/1.00  
% 1.14/1.00  fof(f36,plain,(
% 1.14/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.14/1.00    inference(cnf_transformation,[],[f26])).
% 1.14/1.00  
% 1.14/1.00  fof(f7,axiom,(
% 1.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.00  
% 1.14/1.00  fof(f18,plain,(
% 1.14/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/1.00    inference(ennf_transformation,[],[f7])).
% 1.14/1.00  
% 1.14/1.00  fof(f28,plain,(
% 1.14/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/1.00    inference(nnf_transformation,[],[f18])).
% 1.14/1.00  
% 1.14/1.00  fof(f44,plain,(
% 1.14/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.14/1.00    inference(cnf_transformation,[],[f28])).
% 1.14/1.00  
% 1.14/1.00  fof(f8,axiom,(
% 1.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 1.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.00  
% 1.14/1.00  fof(f19,plain,(
% 1.14/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/1.00    inference(ennf_transformation,[],[f8])).
% 1.14/1.00  
% 1.14/1.00  fof(f20,plain,(
% 1.14/1.00    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/1.00    inference(flattening,[],[f19])).
% 1.14/1.00  
% 1.14/1.00  fof(f45,plain,(
% 1.14/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.14/1.00    inference(cnf_transformation,[],[f20])).
% 1.14/1.00  
% 1.14/1.00  fof(f50,plain,(
% 1.14/1.00    k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)),
% 1.14/1.00    inference(cnf_transformation,[],[f33])).
% 1.14/1.00  
% 1.14/1.00  fof(f5,axiom,(
% 1.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 1.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.00  
% 1.14/1.00  fof(f16,plain,(
% 1.14/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/1.00    inference(ennf_transformation,[],[f5])).
% 1.14/1.00  
% 1.14/1.00  fof(f40,plain,(
% 1.14/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.14/1.00    inference(cnf_transformation,[],[f16])).
% 1.14/1.00  
% 1.14/1.00  fof(f4,axiom,(
% 1.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.00  
% 1.14/1.00  fof(f12,plain,(
% 1.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 1.14/1.00    inference(pure_predicate_removal,[],[f4])).
% 1.14/1.00  
% 1.14/1.00  fof(f14,plain,(
% 1.14/1.00    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/1.00    inference(ennf_transformation,[],[f12])).
% 1.14/1.00  
% 1.14/1.00  fof(f15,plain,(
% 1.14/1.00    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/1.00    inference(flattening,[],[f14])).
% 1.14/1.00  
% 1.14/1.00  fof(f39,plain,(
% 1.14/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.14/1.00    inference(cnf_transformation,[],[f15])).
% 1.14/1.00  
% 1.14/1.00  fof(f49,plain,(
% 1.14/1.00    v4_pre_topc(sK1,sK0)),
% 1.14/1.00    inference(cnf_transformation,[],[f33])).
% 1.14/1.00  
% 1.14/1.00  fof(f2,axiom,(
% 1.14/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.00  
% 1.14/1.00  fof(f37,plain,(
% 1.14/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.14/1.00    inference(cnf_transformation,[],[f2])).
% 1.14/1.00  
% 1.14/1.00  fof(f3,axiom,(
% 1.14/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.00  
% 1.14/1.00  fof(f13,plain,(
% 1.14/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.14/1.00    inference(ennf_transformation,[],[f3])).
% 1.14/1.00  
% 1.14/1.00  fof(f38,plain,(
% 1.14/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.14/1.00    inference(cnf_transformation,[],[f13])).
% 1.14/1.00  
% 1.14/1.00  fof(f42,plain,(
% 1.14/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.14/1.00    inference(cnf_transformation,[],[f27])).
% 1.14/1.00  
% 1.14/1.00  fof(f9,axiom,(
% 1.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 1.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.00  
% 1.14/1.00  fof(f21,plain,(
% 1.14/1.00    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/1.00    inference(ennf_transformation,[],[f9])).
% 1.14/1.00  
% 1.14/1.00  fof(f22,plain,(
% 1.14/1.00    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/1.00    inference(flattening,[],[f21])).
% 1.14/1.00  
% 1.14/1.00  fof(f46,plain,(
% 1.14/1.00    ( ! [X0,X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.14/1.00    inference(cnf_transformation,[],[f22])).
% 1.14/1.00  
% 1.14/1.00  fof(f51,plain,(
% 1.14/1.00    k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)),
% 1.14/1.00    inference(cnf_transformation,[],[f33])).
% 1.14/1.00  
% 1.14/1.00  cnf(c_16,negated_conjecture,
% 1.14/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.14/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_8,plain,
% 1.14/1.00      ( ~ v2_tops_1(X0,X1)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | ~ l1_pre_topc(X1)
% 1.14/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 1.14/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_17,negated_conjecture,
% 1.14/1.00      ( l1_pre_topc(sK0) ),
% 1.14/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_310,plain,
% 1.14/1.00      ( ~ v2_tops_1(X0,X1)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 1.14/1.00      | sK0 != X1 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_311,plain,
% 1.14/1.00      ( ~ v2_tops_1(X0,sK0)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.14/1.00      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_310]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_313,plain,
% 1.14/1.00      ( ~ v2_tops_1(sK1,sK0)
% 1.14/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.14/1.00      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 1.14/1.00      inference(instantiation,[status(thm)],[c_311]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_545,plain,
% 1.14/1.00      ( ~ v2_tops_1(sK1,sK0) | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 1.14/1.00      inference(prop_impl,[status(thm)],[c_16,c_313]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_953,plain,
% 1.14/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 1.14/1.00      | v2_tops_1(sK1,sK0) != iProver_top ),
% 1.14/1.00      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_2,plain,
% 1.14/1.00      ( r1_tarski(X0,X0) ),
% 1.14/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_52,plain,
% 1.14/1.00      ( r1_tarski(sK1,sK1) ),
% 1.14/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_0,plain,
% 1.14/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.14/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_56,plain,
% 1.14/1.00      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 1.14/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_9,plain,
% 1.14/1.00      ( v2_tops_1(X0,X1)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 1.14/1.00      | ~ l1_pre_topc(X1) ),
% 1.14/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_295,plain,
% 1.14/1.00      ( v2_tops_1(X0,X1)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 1.14/1.00      | sK0 != X1 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_296,plain,
% 1.14/1.00      ( v2_tops_1(X0,sK0)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.14/1.00      | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_295]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_405,plain,
% 1.14/1.00      ( v2_tops_1(X0,sK0)
% 1.14/1.00      | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
% 1.14/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 1.14/1.00      | sK1 != X0 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_296]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_406,plain,
% 1.14/1.00      ( v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_405]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_395,plain,
% 1.14/1.00      ( ~ v2_tops_1(X0,sK0)
% 1.14/1.00      | k1_tops_1(sK0,X0) = k1_xboole_0
% 1.14/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 1.14/1.00      | sK1 != X0 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_311]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_396,plain,
% 1.14/1.00      ( ~ v2_tops_1(sK1,sK0) | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_395]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_441,plain,
% 1.14/1.00      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 1.14/1.00      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 1.14/1.00      inference(resolution,[status(thm)],[c_406,c_396]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_11,plain,
% 1.14/1.00      ( ~ v3_tops_1(X0,X1)
% 1.14/1.00      | v2_tops_1(X0,X1)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | ~ l1_pre_topc(X1) ),
% 1.14/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_14,negated_conjecture,
% 1.14/1.00      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 1.14/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_130,plain,
% 1.14/1.00      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 1.14/1.00      inference(prop_impl,[status(thm)],[c_14]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_260,plain,
% 1.14/1.00      ( v2_tops_1(X0,X1)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | ~ l1_pre_topc(X1)
% 1.14/1.00      | k2_tops_1(sK0,sK1) = sK1
% 1.14/1.00      | sK1 != X0
% 1.14/1.00      | sK0 != X1 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_130]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_261,plain,
% 1.14/1.00      ( v2_tops_1(sK1,sK0)
% 1.14/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.14/1.00      | ~ l1_pre_topc(sK0)
% 1.14/1.00      | k2_tops_1(sK0,sK1) = sK1 ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_260]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_263,plain,
% 1.14/1.00      ( v2_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 1.14/1.00      inference(global_propositional_subsumption,
% 1.14/1.00                [status(thm)],
% 1.14/1.00                [c_261,c_17,c_16]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_485,plain,
% 1.14/1.00      ( k2_tops_1(sK0,sK1) = sK1 | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 1.14/1.00      inference(resolution,[status(thm)],[c_263,c_396]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_674,plain,
% 1.14/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.14/1.00      theory(equality) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_1041,plain,
% 1.14/1.00      ( ~ r1_tarski(X0,X1)
% 1.14/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 1.14/1.00      | k2_tops_1(sK0,sK1) != X1
% 1.14/1.00      | sK1 != X0 ),
% 1.14/1.00      inference(instantiation,[status(thm)],[c_674]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_1043,plain,
% 1.14/1.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 1.14/1.00      | ~ r1_tarski(sK1,sK1)
% 1.14/1.00      | k2_tops_1(sK0,sK1) != sK1
% 1.14/1.00      | sK1 != sK1 ),
% 1.14/1.00      inference(instantiation,[status(thm)],[c_1041]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_1101,plain,
% 1.14/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 1.14/1.00      inference(global_propositional_subsumption,
% 1.14/1.00                [status(thm)],
% 1.14/1.00                [c_953,c_52,c_56,c_441,c_485,c_1043]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_6,plain,
% 1.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | ~ l1_pre_topc(X1)
% 1.14/1.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 1.14/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_340,plain,
% 1.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 1.14/1.00      | sK0 != X1 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_341,plain,
% 1.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.14/1.00      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_340]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_380,plain,
% 1.14/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 1.14/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 1.14/1.00      | sK1 != X0 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_341]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_381,plain,
% 1.14/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_380]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_5,plain,
% 1.14/1.00      ( ~ v4_pre_topc(X0,X1)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | ~ l1_pre_topc(X1)
% 1.14/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 1.14/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_15,negated_conjecture,
% 1.14/1.00      ( v4_pre_topc(sK1,sK0) ),
% 1.14/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_236,plain,
% 1.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | ~ l1_pre_topc(X1)
% 1.14/1.00      | k2_pre_topc(X1,X0) = X0
% 1.14/1.00      | sK1 != X0
% 1.14/1.00      | sK0 != X1 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_237,plain,
% 1.14/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.14/1.00      | ~ l1_pre_topc(sK0)
% 1.14/1.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_236]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_239,plain,
% 1.14/1.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 1.14/1.00      inference(global_propositional_subsumption,
% 1.14/1.00                [status(thm)],
% 1.14/1.00                [c_237,c_17,c_16]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_977,plain,
% 1.14/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 1.14/1.00      inference(light_normalisation,[status(thm)],[c_381,c_239]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_1105,plain,
% 1.14/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 1.14/1.00      inference(demodulation,[status(thm)],[c_1101,c_977]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_3,plain,
% 1.14/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.14/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_4,plain,
% 1.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.14/1.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 1.14/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_371,plain,
% 1.14/1.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 1.14/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
% 1.14/1.00      | sK1 != X1 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_372,plain,
% 1.14/1.00      ( k7_subset_1(X0,sK1,X1) = k4_xboole_0(sK1,X1)
% 1.14/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_371]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_1023,plain,
% 1.14/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 1.14/1.00      inference(equality_resolution,[status(thm)],[c_372]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_1107,plain,
% 1.14/1.00      ( k2_tops_1(sK0,sK1) = sK1 ),
% 1.14/1.00      inference(demodulation,[status(thm)],[c_1105,c_3,c_1023]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_7,plain,
% 1.14/1.00      ( v2_tops_1(X0,X1)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | ~ l1_pre_topc(X1)
% 1.14/1.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 1.14/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_325,plain,
% 1.14/1.00      ( v2_tops_1(X0,X1)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | k1_tops_1(X1,X0) != k1_xboole_0
% 1.14/1.00      | sK0 != X1 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_326,plain,
% 1.14/1.00      ( v2_tops_1(X0,sK0)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.14/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_325]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_385,plain,
% 1.14/1.00      ( v2_tops_1(X0,sK0)
% 1.14/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0
% 1.14/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 1.14/1.00      | sK1 != X0 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_326]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_386,plain,
% 1.14/1.00      ( v2_tops_1(sK1,sK0) | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_385]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_12,plain,
% 1.14/1.00      ( v3_tops_1(X0,X1)
% 1.14/1.00      | ~ v2_tops_1(X0,X1)
% 1.14/1.00      | ~ v4_pre_topc(X0,X1)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | ~ l1_pre_topc(X1) ),
% 1.14/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_222,plain,
% 1.14/1.00      ( v3_tops_1(X0,X1)
% 1.14/1.00      | ~ v2_tops_1(X0,X1)
% 1.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.14/1.00      | ~ l1_pre_topc(X1)
% 1.14/1.00      | sK1 != X0
% 1.14/1.00      | sK0 != X1 ),
% 1.14/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_223,plain,
% 1.14/1.00      ( v3_tops_1(sK1,sK0)
% 1.14/1.00      | ~ v2_tops_1(sK1,sK0)
% 1.14/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.14/1.00      | ~ l1_pre_topc(sK0) ),
% 1.14/1.00      inference(unflattening,[status(thm)],[c_222]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_225,plain,
% 1.14/1.00      ( v3_tops_1(sK1,sK0) | ~ v2_tops_1(sK1,sK0) ),
% 1.14/1.00      inference(global_propositional_subsumption,
% 1.14/1.00                [status(thm)],
% 1.14/1.00                [c_223,c_17,c_16]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_13,negated_conjecture,
% 1.14/1.00      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 1.14/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_128,plain,
% 1.14/1.00      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 1.14/1.00      inference(prop_impl,[status(thm)],[c_13]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_248,plain,
% 1.14/1.00      ( ~ v2_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 1.14/1.00      inference(resolution,[status(thm)],[c_225,c_128]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(c_469,plain,
% 1.14/1.00      ( k2_tops_1(sK0,sK1) != sK1 | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 1.14/1.00      inference(resolution,[status(thm)],[c_386,c_248]) ).
% 1.14/1.00  
% 1.14/1.00  cnf(contradiction,plain,
% 1.14/1.00      ( $false ),
% 1.14/1.00      inference(minisat,[status(thm)],[c_1107,c_1101,c_469]) ).
% 1.14/1.00  
% 1.14/1.00  
% 1.14/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.14/1.00  
% 1.14/1.00  ------                               Statistics
% 1.14/1.00  
% 1.14/1.00  ------ General
% 1.14/1.00  
% 1.14/1.00  abstr_ref_over_cycles:                  0
% 1.14/1.00  abstr_ref_under_cycles:                 0
% 1.14/1.00  gc_basic_clause_elim:                   0
% 1.14/1.00  forced_gc_time:                         0
% 1.14/1.00  parsing_time:                           0.009
% 1.14/1.00  unif_index_cands_time:                  0.
% 1.14/1.00  unif_index_add_time:                    0.
% 1.14/1.00  orderings_time:                         0.
% 1.14/1.00  out_proof_time:                         0.008
% 1.14/1.00  total_time:                             0.064
% 1.14/1.00  num_of_symbols:                         47
% 1.14/1.00  num_of_terms:                           558
% 1.14/1.00  
% 1.14/1.00  ------ Preprocessing
% 1.14/1.00  
% 1.14/1.00  num_of_splits:                          0
% 1.14/1.00  num_of_split_atoms:                     0
% 1.14/1.00  num_of_reused_defs:                     0
% 1.14/1.00  num_eq_ax_congr_red:                    8
% 1.14/1.00  num_of_sem_filtered_clauses:            1
% 1.14/1.00  num_of_subtypes:                        0
% 1.14/1.00  monotx_restored_types:                  0
% 1.14/1.00  sat_num_of_epr_types:                   0
% 1.14/1.00  sat_num_of_non_cyclic_types:            0
% 1.14/1.00  sat_guarded_non_collapsed_types:        0
% 1.14/1.00  num_pure_diseq_elim:                    0
% 1.14/1.00  simp_replaced_by:                       0
% 1.14/1.00  res_preprocessed:                       76
% 1.14/1.00  prep_upred:                             0
% 1.14/1.00  prep_unflattend:                        19
% 1.14/1.00  smt_new_axioms:                         0
% 1.14/1.00  pred_elim_cands:                        2
% 1.14/1.00  pred_elim:                              4
% 1.14/1.00  pred_elim_cl:                           5
% 1.14/1.00  pred_elim_cycles:                       6
% 1.14/1.00  merged_defs:                            20
% 1.14/1.00  merged_defs_ncl:                        0
% 1.14/1.00  bin_hyper_res:                          20
% 1.14/1.00  prep_cycles:                            4
% 1.14/1.00  pred_elim_time:                         0.005
% 1.14/1.00  splitting_time:                         0.
% 1.14/1.00  sem_filter_time:                        0.
% 1.14/1.00  monotx_time:                            0.
% 1.14/1.00  subtype_inf_time:                       0.
% 1.14/1.00  
% 1.14/1.00  ------ Problem properties
% 1.14/1.00  
% 1.14/1.00  clauses:                                12
% 1.14/1.00  conjectures:                            0
% 1.14/1.00  epr:                                    2
% 1.14/1.00  horn:                                   11
% 1.14/1.00  ground:                                 8
% 1.14/1.00  unary:                                  4
% 1.14/1.00  binary:                                 7
% 1.14/1.00  lits:                                   21
% 1.14/1.00  lits_eq:                                10
% 1.14/1.00  fd_pure:                                0
% 1.14/1.00  fd_pseudo:                              0
% 1.14/1.00  fd_cond:                                0
% 1.14/1.00  fd_pseudo_cond:                         1
% 1.14/1.00  ac_symbols:                             0
% 1.14/1.00  
% 1.14/1.00  ------ Propositional Solver
% 1.14/1.00  
% 1.14/1.00  prop_solver_calls:                      24
% 1.14/1.00  prop_fast_solver_calls:                 427
% 1.14/1.00  smt_solver_calls:                       0
% 1.14/1.00  smt_fast_solver_calls:                  0
% 1.14/1.00  prop_num_of_clauses:                    187
% 1.14/1.00  prop_preprocess_simplified:             1600
% 1.14/1.00  prop_fo_subsumed:                       7
% 1.14/1.00  prop_solver_time:                       0.
% 1.14/1.00  smt_solver_time:                        0.
% 1.14/1.00  smt_fast_solver_time:                   0.
% 1.14/1.00  prop_fast_solver_time:                  0.
% 1.14/1.00  prop_unsat_core_time:                   0.
% 1.14/1.00  
% 1.14/1.00  ------ QBF
% 1.14/1.00  
% 1.14/1.00  qbf_q_res:                              0
% 1.14/1.00  qbf_num_tautologies:                    0
% 1.14/1.00  qbf_prep_cycles:                        0
% 1.14/1.00  
% 1.14/1.00  ------ BMC1
% 1.14/1.00  
% 1.14/1.00  bmc1_current_bound:                     -1
% 1.14/1.00  bmc1_last_solved_bound:                 -1
% 1.14/1.00  bmc1_unsat_core_size:                   -1
% 1.14/1.00  bmc1_unsat_core_parents_size:           -1
% 1.14/1.00  bmc1_merge_next_fun:                    0
% 1.14/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.14/1.00  
% 1.14/1.00  ------ Instantiation
% 1.14/1.00  
% 1.14/1.00  inst_num_of_clauses:                    43
% 1.14/1.00  inst_num_in_passive:                    10
% 1.14/1.00  inst_num_in_active:                     32
% 1.14/1.00  inst_num_in_unprocessed:                1
% 1.14/1.00  inst_num_of_loops:                      40
% 1.14/1.00  inst_num_of_learning_restarts:          0
% 1.14/1.00  inst_num_moves_active_passive:          6
% 1.14/1.00  inst_lit_activity:                      0
% 1.14/1.00  inst_lit_activity_moves:                0
% 1.14/1.00  inst_num_tautologies:                   0
% 1.14/1.00  inst_num_prop_implied:                  0
% 1.14/1.00  inst_num_existing_simplified:           0
% 1.14/1.00  inst_num_eq_res_simplified:             0
% 1.14/1.00  inst_num_child_elim:                    0
% 1.14/1.00  inst_num_of_dismatching_blockings:      0
% 1.14/1.00  inst_num_of_non_proper_insts:           19
% 1.14/1.00  inst_num_of_duplicates:                 0
% 1.14/1.00  inst_inst_num_from_inst_to_res:         0
% 1.14/1.00  inst_dismatching_checking_time:         0.
% 1.14/1.00  
% 1.14/1.00  ------ Resolution
% 1.14/1.00  
% 1.14/1.00  res_num_of_clauses:                     0
% 1.14/1.00  res_num_in_passive:                     0
% 1.14/1.00  res_num_in_active:                      0
% 1.14/1.00  res_num_of_loops:                       80
% 1.14/1.00  res_forward_subset_subsumed:            2
% 1.14/1.00  res_backward_subset_subsumed:           0
% 1.14/1.00  res_forward_subsumed:                   0
% 1.14/1.00  res_backward_subsumed:                  0
% 1.14/1.00  res_forward_subsumption_resolution:     0
% 1.14/1.00  res_backward_subsumption_resolution:    0
% 1.14/1.00  res_clause_to_clause_subsumption:       38
% 1.14/1.00  res_orphan_elimination:                 0
% 1.14/1.00  res_tautology_del:                      48
% 1.14/1.00  res_num_eq_res_simplified:              0
% 1.14/1.00  res_num_sel_changes:                    0
% 1.14/1.00  res_moves_from_active_to_pass:          0
% 1.14/1.00  
% 1.14/1.00  ------ Superposition
% 1.14/1.00  
% 1.14/1.00  sup_time_total:                         0.
% 1.14/1.00  sup_time_generating:                    0.
% 1.14/1.00  sup_time_sim_full:                      0.
% 1.14/1.00  sup_time_sim_immed:                     0.
% 1.14/1.00  
% 1.14/1.00  sup_num_of_clauses:                     12
% 1.14/1.00  sup_num_in_active:                      5
% 1.14/1.00  sup_num_in_passive:                     7
% 1.14/1.00  sup_num_of_loops:                       7
% 1.14/1.00  sup_fw_superposition:                   1
% 1.14/1.00  sup_bw_superposition:                   1
% 1.14/1.00  sup_immediate_simplified:               3
% 1.14/1.00  sup_given_eliminated:                   0
% 1.14/1.00  comparisons_done:                       0
% 1.14/1.00  comparisons_avoided:                    0
% 1.14/1.00  
% 1.14/1.00  ------ Simplifications
% 1.14/1.00  
% 1.14/1.00  
% 1.14/1.00  sim_fw_subset_subsumed:                 0
% 1.14/1.00  sim_bw_subset_subsumed:                 1
% 1.14/1.00  sim_fw_subsumed:                        1
% 1.14/1.00  sim_bw_subsumed:                        0
% 1.14/1.00  sim_fw_subsumption_res:                 0
% 1.14/1.00  sim_bw_subsumption_res:                 0
% 1.14/1.00  sim_tautology_del:                      0
% 1.14/1.00  sim_eq_tautology_del:                   0
% 1.14/1.00  sim_eq_res_simp:                        0
% 1.14/1.00  sim_fw_demodulated:                     1
% 1.14/1.00  sim_bw_demodulated:                     2
% 1.14/1.00  sim_light_normalised:                   2
% 1.14/1.00  sim_joinable_taut:                      0
% 1.14/1.00  sim_joinable_simp:                      0
% 1.14/1.00  sim_ac_normalised:                      0
% 1.14/1.00  sim_smt_subsumption:                    0
% 1.14/1.00  
%------------------------------------------------------------------------------
