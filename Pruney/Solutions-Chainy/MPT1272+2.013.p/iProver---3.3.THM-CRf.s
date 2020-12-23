%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:19 EST 2020

% Result     : Theorem 1.01s
% Output     : CNFRefutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 289 expanded)
%              Number of clauses        :   53 (  84 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :   19
%              Number of atoms          :  298 (1080 expanded)
%              Number of equality atoms :   72 (  94 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0)
        & v3_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            & v3_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          & v3_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f27,f26])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_634,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_225,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_226,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_9,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(k2_pre_topc(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,negated_conjecture,
    ( v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_212,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_213,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_215,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_213,c_16,c_15])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0
    | k2_pre_topc(sK0,sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_226,c_215])).

cnf(c_332,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_629,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_702,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_817,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_15,c_332,c_702])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_256,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_633,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_821,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_817,c_633])).

cnf(c_18,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_703,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_1287,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_821,c_18,c_703])).

cnf(c_1296,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_1287])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_273,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_705,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_706,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_1313,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1296,c_18,c_706])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_635,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_637,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1050,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_637])).

cnf(c_1319,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1313,c_1050])).

cnf(c_11,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_240,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_241,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_7,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v2_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_186,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),X0) != k3_subset_1(u1_struct_0(sK0),sK1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_187,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_191,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(X0,sK0)
    | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_187,c_16])).

cnf(c_192,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(resolution,[status(thm)],[c_241,c_192])).

cnf(c_630,plain,
    ( k1_tops_1(sK0,X0) != k1_xboole_0
    | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_999,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_630])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1319,c_999,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.01/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.01/0.96  
% 1.01/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.01/0.96  
% 1.01/0.96  ------  iProver source info
% 1.01/0.96  
% 1.01/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.01/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.01/0.96  git: non_committed_changes: false
% 1.01/0.96  git: last_make_outside_of_git: false
% 1.01/0.96  
% 1.01/0.96  ------ 
% 1.01/0.96  
% 1.01/0.96  ------ Input Options
% 1.01/0.96  
% 1.01/0.96  --out_options                           all
% 1.01/0.96  --tptp_safe_out                         true
% 1.01/0.96  --problem_path                          ""
% 1.01/0.96  --include_path                          ""
% 1.01/0.96  --clausifier                            res/vclausify_rel
% 1.01/0.96  --clausifier_options                    --mode clausify
% 1.01/0.96  --stdin                                 false
% 1.01/0.96  --stats_out                             all
% 1.01/0.96  
% 1.01/0.96  ------ General Options
% 1.01/0.96  
% 1.01/0.96  --fof                                   false
% 1.01/0.96  --time_out_real                         305.
% 1.01/0.96  --time_out_virtual                      -1.
% 1.01/0.96  --symbol_type_check                     false
% 1.01/0.96  --clausify_out                          false
% 1.01/0.96  --sig_cnt_out                           false
% 1.01/0.96  --trig_cnt_out                          false
% 1.01/0.96  --trig_cnt_out_tolerance                1.
% 1.01/0.96  --trig_cnt_out_sk_spl                   false
% 1.01/0.96  --abstr_cl_out                          false
% 1.01/0.96  
% 1.01/0.96  ------ Global Options
% 1.01/0.96  
% 1.01/0.96  --schedule                              default
% 1.01/0.96  --add_important_lit                     false
% 1.01/0.96  --prop_solver_per_cl                    1000
% 1.01/0.96  --min_unsat_core                        false
% 1.01/0.96  --soft_assumptions                      false
% 1.01/0.96  --soft_lemma_size                       3
% 1.01/0.96  --prop_impl_unit_size                   0
% 1.01/0.96  --prop_impl_unit                        []
% 1.01/0.96  --share_sel_clauses                     true
% 1.01/0.96  --reset_solvers                         false
% 1.01/0.96  --bc_imp_inh                            [conj_cone]
% 1.01/0.96  --conj_cone_tolerance                   3.
% 1.01/0.96  --extra_neg_conj                        none
% 1.01/0.96  --large_theory_mode                     true
% 1.01/0.96  --prolific_symb_bound                   200
% 1.01/0.96  --lt_threshold                          2000
% 1.01/0.96  --clause_weak_htbl                      true
% 1.01/0.96  --gc_record_bc_elim                     false
% 1.01/0.96  
% 1.01/0.96  ------ Preprocessing Options
% 1.01/0.96  
% 1.01/0.96  --preprocessing_flag                    true
% 1.01/0.96  --time_out_prep_mult                    0.1
% 1.01/0.96  --splitting_mode                        input
% 1.01/0.96  --splitting_grd                         true
% 1.01/0.96  --splitting_cvd                         false
% 1.01/0.96  --splitting_cvd_svl                     false
% 1.01/0.96  --splitting_nvd                         32
% 1.01/0.96  --sub_typing                            true
% 1.01/0.96  --prep_gs_sim                           true
% 1.01/0.96  --prep_unflatten                        true
% 1.01/0.96  --prep_res_sim                          true
% 1.01/0.96  --prep_upred                            true
% 1.01/0.96  --prep_sem_filter                       exhaustive
% 1.01/0.96  --prep_sem_filter_out                   false
% 1.01/0.96  --pred_elim                             true
% 1.01/0.96  --res_sim_input                         true
% 1.01/0.96  --eq_ax_congr_red                       true
% 1.01/0.96  --pure_diseq_elim                       true
% 1.01/0.96  --brand_transform                       false
% 1.01/0.96  --non_eq_to_eq                          false
% 1.01/0.96  --prep_def_merge                        true
% 1.01/0.96  --prep_def_merge_prop_impl              false
% 1.01/0.96  --prep_def_merge_mbd                    true
% 1.01/0.96  --prep_def_merge_tr_red                 false
% 1.01/0.96  --prep_def_merge_tr_cl                  false
% 1.01/0.96  --smt_preprocessing                     true
% 1.01/0.96  --smt_ac_axioms                         fast
% 1.01/0.96  --preprocessed_out                      false
% 1.01/0.96  --preprocessed_stats                    false
% 1.01/0.96  
% 1.01/0.96  ------ Abstraction refinement Options
% 1.01/0.96  
% 1.01/0.96  --abstr_ref                             []
% 1.01/0.96  --abstr_ref_prep                        false
% 1.01/0.96  --abstr_ref_until_sat                   false
% 1.01/0.96  --abstr_ref_sig_restrict                funpre
% 1.01/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/0.96  --abstr_ref_under                       []
% 1.01/0.96  
% 1.01/0.96  ------ SAT Options
% 1.01/0.96  
% 1.01/0.96  --sat_mode                              false
% 1.01/0.96  --sat_fm_restart_options                ""
% 1.01/0.96  --sat_gr_def                            false
% 1.01/0.96  --sat_epr_types                         true
% 1.01/0.96  --sat_non_cyclic_types                  false
% 1.01/0.96  --sat_finite_models                     false
% 1.01/0.96  --sat_fm_lemmas                         false
% 1.01/0.96  --sat_fm_prep                           false
% 1.01/0.96  --sat_fm_uc_incr                        true
% 1.01/0.96  --sat_out_model                         small
% 1.01/0.96  --sat_out_clauses                       false
% 1.01/0.96  
% 1.01/0.96  ------ QBF Options
% 1.01/0.96  
% 1.01/0.96  --qbf_mode                              false
% 1.01/0.96  --qbf_elim_univ                         false
% 1.01/0.96  --qbf_dom_inst                          none
% 1.01/0.96  --qbf_dom_pre_inst                      false
% 1.01/0.96  --qbf_sk_in                             false
% 1.01/0.96  --qbf_pred_elim                         true
% 1.01/0.96  --qbf_split                             512
% 1.01/0.96  
% 1.01/0.96  ------ BMC1 Options
% 1.01/0.96  
% 1.01/0.96  --bmc1_incremental                      false
% 1.01/0.96  --bmc1_axioms                           reachable_all
% 1.01/0.96  --bmc1_min_bound                        0
% 1.01/0.96  --bmc1_max_bound                        -1
% 1.01/0.96  --bmc1_max_bound_default                -1
% 1.01/0.96  --bmc1_symbol_reachability              true
% 1.01/0.96  --bmc1_property_lemmas                  false
% 1.01/0.96  --bmc1_k_induction                      false
% 1.01/0.96  --bmc1_non_equiv_states                 false
% 1.01/0.96  --bmc1_deadlock                         false
% 1.01/0.96  --bmc1_ucm                              false
% 1.01/0.96  --bmc1_add_unsat_core                   none
% 1.01/0.96  --bmc1_unsat_core_children              false
% 1.01/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/0.96  --bmc1_out_stat                         full
% 1.01/0.96  --bmc1_ground_init                      false
% 1.01/0.96  --bmc1_pre_inst_next_state              false
% 1.01/0.96  --bmc1_pre_inst_state                   false
% 1.01/0.96  --bmc1_pre_inst_reach_state             false
% 1.01/0.96  --bmc1_out_unsat_core                   false
% 1.01/0.96  --bmc1_aig_witness_out                  false
% 1.01/0.96  --bmc1_verbose                          false
% 1.01/0.96  --bmc1_dump_clauses_tptp                false
% 1.01/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.01/0.96  --bmc1_dump_file                        -
% 1.01/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.01/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.01/0.96  --bmc1_ucm_extend_mode                  1
% 1.01/0.96  --bmc1_ucm_init_mode                    2
% 1.01/0.96  --bmc1_ucm_cone_mode                    none
% 1.01/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.01/0.96  --bmc1_ucm_relax_model                  4
% 1.01/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.01/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/0.96  --bmc1_ucm_layered_model                none
% 1.01/0.96  --bmc1_ucm_max_lemma_size               10
% 1.01/0.96  
% 1.01/0.96  ------ AIG Options
% 1.01/0.96  
% 1.01/0.96  --aig_mode                              false
% 1.01/0.96  
% 1.01/0.96  ------ Instantiation Options
% 1.01/0.96  
% 1.01/0.96  --instantiation_flag                    true
% 1.01/0.96  --inst_sos_flag                         false
% 1.01/0.96  --inst_sos_phase                        true
% 1.01/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/0.96  --inst_lit_sel_side                     num_symb
% 1.01/0.96  --inst_solver_per_active                1400
% 1.01/0.96  --inst_solver_calls_frac                1.
% 1.01/0.96  --inst_passive_queue_type               priority_queues
% 1.01/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/0.96  --inst_passive_queues_freq              [25;2]
% 1.01/0.96  --inst_dismatching                      true
% 1.01/0.96  --inst_eager_unprocessed_to_passive     true
% 1.01/0.96  --inst_prop_sim_given                   true
% 1.01/0.96  --inst_prop_sim_new                     false
% 1.01/0.96  --inst_subs_new                         false
% 1.01/0.96  --inst_eq_res_simp                      false
% 1.01/0.96  --inst_subs_given                       false
% 1.01/0.96  --inst_orphan_elimination               true
% 1.01/0.96  --inst_learning_loop_flag               true
% 1.01/0.96  --inst_learning_start                   3000
% 1.01/0.96  --inst_learning_factor                  2
% 1.01/0.96  --inst_start_prop_sim_after_learn       3
% 1.01/0.96  --inst_sel_renew                        solver
% 1.01/0.96  --inst_lit_activity_flag                true
% 1.01/0.96  --inst_restr_to_given                   false
% 1.01/0.96  --inst_activity_threshold               500
% 1.01/0.96  --inst_out_proof                        true
% 1.01/0.96  
% 1.01/0.96  ------ Resolution Options
% 1.01/0.96  
% 1.01/0.96  --resolution_flag                       true
% 1.01/0.96  --res_lit_sel                           adaptive
% 1.01/0.96  --res_lit_sel_side                      none
% 1.01/0.96  --res_ordering                          kbo
% 1.01/0.96  --res_to_prop_solver                    active
% 1.01/0.96  --res_prop_simpl_new                    false
% 1.01/0.96  --res_prop_simpl_given                  true
% 1.01/0.96  --res_passive_queue_type                priority_queues
% 1.01/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/0.96  --res_passive_queues_freq               [15;5]
% 1.01/0.96  --res_forward_subs                      full
% 1.01/0.96  --res_backward_subs                     full
% 1.01/0.96  --res_forward_subs_resolution           true
% 1.01/0.96  --res_backward_subs_resolution          true
% 1.01/0.96  --res_orphan_elimination                true
% 1.01/0.96  --res_time_limit                        2.
% 1.01/0.96  --res_out_proof                         true
% 1.01/0.96  
% 1.01/0.96  ------ Superposition Options
% 1.01/0.96  
% 1.01/0.96  --superposition_flag                    true
% 1.01/0.96  --sup_passive_queue_type                priority_queues
% 1.01/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.01/0.96  --demod_completeness_check              fast
% 1.01/0.96  --demod_use_ground                      true
% 1.01/0.96  --sup_to_prop_solver                    passive
% 1.01/0.96  --sup_prop_simpl_new                    true
% 1.01/0.96  --sup_prop_simpl_given                  true
% 1.01/0.96  --sup_fun_splitting                     false
% 1.01/0.96  --sup_smt_interval                      50000
% 1.01/0.96  
% 1.01/0.96  ------ Superposition Simplification Setup
% 1.01/0.96  
% 1.01/0.96  --sup_indices_passive                   []
% 1.01/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.96  --sup_full_bw                           [BwDemod]
% 1.01/0.96  --sup_immed_triv                        [TrivRules]
% 1.01/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.96  --sup_immed_bw_main                     []
% 1.01/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.96  
% 1.01/0.96  ------ Combination Options
% 1.01/0.96  
% 1.01/0.96  --comb_res_mult                         3
% 1.01/0.96  --comb_sup_mult                         2
% 1.01/0.96  --comb_inst_mult                        10
% 1.01/0.96  
% 1.01/0.96  ------ Debug Options
% 1.01/0.96  
% 1.01/0.96  --dbg_backtrace                         false
% 1.01/0.96  --dbg_dump_prop_clauses                 false
% 1.01/0.96  --dbg_dump_prop_clauses_file            -
% 1.01/0.96  --dbg_out_stat                          false
% 1.01/0.96  ------ Parsing...
% 1.01/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.01/0.96  
% 1.01/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.01/0.96  
% 1.01/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.01/0.96  
% 1.01/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.01/0.96  ------ Proving...
% 1.01/0.96  ------ Problem Properties 
% 1.01/0.96  
% 1.01/0.96  
% 1.01/0.96  clauses                                 10
% 1.01/0.96  conjectures                             1
% 1.01/0.96  EPR                                     3
% 1.01/0.96  Horn                                    10
% 1.01/0.96  unary                                   3
% 1.01/0.96  binary                                  4
% 1.01/0.96  lits                                    21
% 1.01/0.96  lits eq                                 5
% 1.01/0.96  fd_pure                                 0
% 1.01/0.96  fd_pseudo                               0
% 1.01/0.96  fd_cond                                 0
% 1.01/0.96  fd_pseudo_cond                          1
% 1.01/0.96  AC symbols                              0
% 1.01/0.96  
% 1.01/0.96  ------ Schedule dynamic 5 is on 
% 1.01/0.96  
% 1.01/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.01/0.96  
% 1.01/0.96  
% 1.01/0.96  ------ 
% 1.01/0.96  Current options:
% 1.01/0.96  ------ 
% 1.01/0.96  
% 1.01/0.96  ------ Input Options
% 1.01/0.96  
% 1.01/0.96  --out_options                           all
% 1.01/0.96  --tptp_safe_out                         true
% 1.01/0.96  --problem_path                          ""
% 1.01/0.96  --include_path                          ""
% 1.01/0.96  --clausifier                            res/vclausify_rel
% 1.01/0.96  --clausifier_options                    --mode clausify
% 1.01/0.96  --stdin                                 false
% 1.01/0.96  --stats_out                             all
% 1.01/0.96  
% 1.01/0.96  ------ General Options
% 1.01/0.96  
% 1.01/0.96  --fof                                   false
% 1.01/0.96  --time_out_real                         305.
% 1.01/0.96  --time_out_virtual                      -1.
% 1.01/0.96  --symbol_type_check                     false
% 1.01/0.96  --clausify_out                          false
% 1.01/0.96  --sig_cnt_out                           false
% 1.01/0.96  --trig_cnt_out                          false
% 1.01/0.96  --trig_cnt_out_tolerance                1.
% 1.01/0.96  --trig_cnt_out_sk_spl                   false
% 1.01/0.96  --abstr_cl_out                          false
% 1.01/0.96  
% 1.01/0.96  ------ Global Options
% 1.01/0.96  
% 1.01/0.96  --schedule                              default
% 1.01/0.96  --add_important_lit                     false
% 1.01/0.96  --prop_solver_per_cl                    1000
% 1.01/0.96  --min_unsat_core                        false
% 1.01/0.96  --soft_assumptions                      false
% 1.01/0.96  --soft_lemma_size                       3
% 1.01/0.96  --prop_impl_unit_size                   0
% 1.01/0.96  --prop_impl_unit                        []
% 1.01/0.96  --share_sel_clauses                     true
% 1.01/0.96  --reset_solvers                         false
% 1.01/0.96  --bc_imp_inh                            [conj_cone]
% 1.01/0.96  --conj_cone_tolerance                   3.
% 1.01/0.96  --extra_neg_conj                        none
% 1.01/0.96  --large_theory_mode                     true
% 1.01/0.96  --prolific_symb_bound                   200
% 1.01/0.96  --lt_threshold                          2000
% 1.01/0.96  --clause_weak_htbl                      true
% 1.01/0.96  --gc_record_bc_elim                     false
% 1.01/0.96  
% 1.01/0.96  ------ Preprocessing Options
% 1.01/0.96  
% 1.01/0.96  --preprocessing_flag                    true
% 1.01/0.96  --time_out_prep_mult                    0.1
% 1.01/0.96  --splitting_mode                        input
% 1.01/0.96  --splitting_grd                         true
% 1.01/0.96  --splitting_cvd                         false
% 1.01/0.96  --splitting_cvd_svl                     false
% 1.01/0.96  --splitting_nvd                         32
% 1.01/0.96  --sub_typing                            true
% 1.01/0.96  --prep_gs_sim                           true
% 1.01/0.96  --prep_unflatten                        true
% 1.01/0.96  --prep_res_sim                          true
% 1.01/0.96  --prep_upred                            true
% 1.01/0.96  --prep_sem_filter                       exhaustive
% 1.01/0.96  --prep_sem_filter_out                   false
% 1.01/0.96  --pred_elim                             true
% 1.01/0.96  --res_sim_input                         true
% 1.01/0.96  --eq_ax_congr_red                       true
% 1.01/0.96  --pure_diseq_elim                       true
% 1.01/0.96  --brand_transform                       false
% 1.01/0.96  --non_eq_to_eq                          false
% 1.01/0.96  --prep_def_merge                        true
% 1.01/0.96  --prep_def_merge_prop_impl              false
% 1.01/0.96  --prep_def_merge_mbd                    true
% 1.01/0.96  --prep_def_merge_tr_red                 false
% 1.01/0.96  --prep_def_merge_tr_cl                  false
% 1.01/0.96  --smt_preprocessing                     true
% 1.01/0.96  --smt_ac_axioms                         fast
% 1.01/0.96  --preprocessed_out                      false
% 1.01/0.96  --preprocessed_stats                    false
% 1.01/0.96  
% 1.01/0.96  ------ Abstraction refinement Options
% 1.01/0.96  
% 1.01/0.96  --abstr_ref                             []
% 1.01/0.96  --abstr_ref_prep                        false
% 1.01/0.96  --abstr_ref_until_sat                   false
% 1.01/0.96  --abstr_ref_sig_restrict                funpre
% 1.01/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/0.96  --abstr_ref_under                       []
% 1.01/0.96  
% 1.01/0.96  ------ SAT Options
% 1.01/0.96  
% 1.01/0.96  --sat_mode                              false
% 1.01/0.96  --sat_fm_restart_options                ""
% 1.01/0.96  --sat_gr_def                            false
% 1.01/0.96  --sat_epr_types                         true
% 1.01/0.96  --sat_non_cyclic_types                  false
% 1.01/0.96  --sat_finite_models                     false
% 1.01/0.96  --sat_fm_lemmas                         false
% 1.01/0.96  --sat_fm_prep                           false
% 1.01/0.96  --sat_fm_uc_incr                        true
% 1.01/0.96  --sat_out_model                         small
% 1.01/0.96  --sat_out_clauses                       false
% 1.01/0.96  
% 1.01/0.96  ------ QBF Options
% 1.01/0.96  
% 1.01/0.96  --qbf_mode                              false
% 1.01/0.96  --qbf_elim_univ                         false
% 1.01/0.96  --qbf_dom_inst                          none
% 1.01/0.96  --qbf_dom_pre_inst                      false
% 1.01/0.96  --qbf_sk_in                             false
% 1.01/0.96  --qbf_pred_elim                         true
% 1.01/0.96  --qbf_split                             512
% 1.01/0.96  
% 1.01/0.96  ------ BMC1 Options
% 1.01/0.96  
% 1.01/0.96  --bmc1_incremental                      false
% 1.01/0.96  --bmc1_axioms                           reachable_all
% 1.01/0.96  --bmc1_min_bound                        0
% 1.01/0.96  --bmc1_max_bound                        -1
% 1.01/0.96  --bmc1_max_bound_default                -1
% 1.01/0.96  --bmc1_symbol_reachability              true
% 1.01/0.96  --bmc1_property_lemmas                  false
% 1.01/0.96  --bmc1_k_induction                      false
% 1.01/0.96  --bmc1_non_equiv_states                 false
% 1.01/0.96  --bmc1_deadlock                         false
% 1.01/0.96  --bmc1_ucm                              false
% 1.01/0.96  --bmc1_add_unsat_core                   none
% 1.01/0.96  --bmc1_unsat_core_children              false
% 1.01/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/0.96  --bmc1_out_stat                         full
% 1.01/0.96  --bmc1_ground_init                      false
% 1.01/0.96  --bmc1_pre_inst_next_state              false
% 1.01/0.96  --bmc1_pre_inst_state                   false
% 1.01/0.96  --bmc1_pre_inst_reach_state             false
% 1.01/0.96  --bmc1_out_unsat_core                   false
% 1.01/0.96  --bmc1_aig_witness_out                  false
% 1.01/0.96  --bmc1_verbose                          false
% 1.01/0.96  --bmc1_dump_clauses_tptp                false
% 1.01/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.01/0.96  --bmc1_dump_file                        -
% 1.01/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.01/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.01/0.96  --bmc1_ucm_extend_mode                  1
% 1.01/0.96  --bmc1_ucm_init_mode                    2
% 1.01/0.96  --bmc1_ucm_cone_mode                    none
% 1.01/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.01/0.96  --bmc1_ucm_relax_model                  4
% 1.01/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.01/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/0.96  --bmc1_ucm_layered_model                none
% 1.01/0.96  --bmc1_ucm_max_lemma_size               10
% 1.01/0.96  
% 1.01/0.96  ------ AIG Options
% 1.01/0.96  
% 1.01/0.96  --aig_mode                              false
% 1.01/0.96  
% 1.01/0.96  ------ Instantiation Options
% 1.01/0.96  
% 1.01/0.96  --instantiation_flag                    true
% 1.01/0.96  --inst_sos_flag                         false
% 1.01/0.96  --inst_sos_phase                        true
% 1.01/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/0.96  --inst_lit_sel_side                     none
% 1.01/0.96  --inst_solver_per_active                1400
% 1.01/0.96  --inst_solver_calls_frac                1.
% 1.01/0.96  --inst_passive_queue_type               priority_queues
% 1.01/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/0.96  --inst_passive_queues_freq              [25;2]
% 1.01/0.96  --inst_dismatching                      true
% 1.01/0.96  --inst_eager_unprocessed_to_passive     true
% 1.01/0.96  --inst_prop_sim_given                   true
% 1.01/0.96  --inst_prop_sim_new                     false
% 1.01/0.96  --inst_subs_new                         false
% 1.01/0.96  --inst_eq_res_simp                      false
% 1.01/0.96  --inst_subs_given                       false
% 1.01/0.96  --inst_orphan_elimination               true
% 1.01/0.96  --inst_learning_loop_flag               true
% 1.01/0.96  --inst_learning_start                   3000
% 1.01/0.96  --inst_learning_factor                  2
% 1.01/0.96  --inst_start_prop_sim_after_learn       3
% 1.01/0.96  --inst_sel_renew                        solver
% 1.01/0.96  --inst_lit_activity_flag                true
% 1.01/0.96  --inst_restr_to_given                   false
% 1.01/0.96  --inst_activity_threshold               500
% 1.01/0.96  --inst_out_proof                        true
% 1.01/0.96  
% 1.01/0.96  ------ Resolution Options
% 1.01/0.96  
% 1.01/0.96  --resolution_flag                       false
% 1.01/0.96  --res_lit_sel                           adaptive
% 1.01/0.96  --res_lit_sel_side                      none
% 1.01/0.96  --res_ordering                          kbo
% 1.01/0.96  --res_to_prop_solver                    active
% 1.01/0.96  --res_prop_simpl_new                    false
% 1.01/0.96  --res_prop_simpl_given                  true
% 1.01/0.96  --res_passive_queue_type                priority_queues
% 1.01/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/0.96  --res_passive_queues_freq               [15;5]
% 1.01/0.96  --res_forward_subs                      full
% 1.01/0.96  --res_backward_subs                     full
% 1.01/0.96  --res_forward_subs_resolution           true
% 1.01/0.96  --res_backward_subs_resolution          true
% 1.01/0.96  --res_orphan_elimination                true
% 1.01/0.96  --res_time_limit                        2.
% 1.01/0.96  --res_out_proof                         true
% 1.01/0.96  
% 1.01/0.96  ------ Superposition Options
% 1.01/0.96  
% 1.01/0.96  --superposition_flag                    true
% 1.01/0.96  --sup_passive_queue_type                priority_queues
% 1.01/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.01/0.96  --demod_completeness_check              fast
% 1.01/0.96  --demod_use_ground                      true
% 1.01/0.96  --sup_to_prop_solver                    passive
% 1.01/0.96  --sup_prop_simpl_new                    true
% 1.01/0.96  --sup_prop_simpl_given                  true
% 1.01/0.96  --sup_fun_splitting                     false
% 1.01/0.96  --sup_smt_interval                      50000
% 1.01/0.96  
% 1.01/0.96  ------ Superposition Simplification Setup
% 1.01/0.96  
% 1.01/0.96  --sup_indices_passive                   []
% 1.01/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.96  --sup_full_bw                           [BwDemod]
% 1.01/0.96  --sup_immed_triv                        [TrivRules]
% 1.01/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.96  --sup_immed_bw_main                     []
% 1.01/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.96  
% 1.01/0.96  ------ Combination Options
% 1.01/0.96  
% 1.01/0.96  --comb_res_mult                         3
% 1.01/0.96  --comb_sup_mult                         2
% 1.01/0.96  --comb_inst_mult                        10
% 1.01/0.96  
% 1.01/0.96  ------ Debug Options
% 1.01/0.96  
% 1.01/0.96  --dbg_backtrace                         false
% 1.01/0.96  --dbg_dump_prop_clauses                 false
% 1.01/0.96  --dbg_dump_prop_clauses_file            -
% 1.01/0.96  --dbg_out_stat                          false
% 1.01/0.96  
% 1.01/0.96  
% 1.01/0.96  
% 1.01/0.96  
% 1.01/0.96  ------ Proving...
% 1.01/0.96  
% 1.01/0.96  
% 1.01/0.96  % SZS status Theorem for theBenchmark.p
% 1.01/0.96  
% 1.01/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 1.01/0.96  
% 1.01/0.96  fof(f9,conjecture,(
% 1.01/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.01/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/0.96  
% 1.01/0.96  fof(f10,negated_conjecture,(
% 1.01/0.96    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.01/0.96    inference(negated_conjecture,[],[f9])).
% 1.01/0.96  
% 1.01/0.96  fof(f19,plain,(
% 1.01/0.96    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.01/0.96    inference(ennf_transformation,[],[f10])).
% 1.01/0.96  
% 1.01/0.96  fof(f20,plain,(
% 1.01/0.96    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.01/0.96    inference(flattening,[],[f19])).
% 1.01/0.96  
% 1.01/0.96  fof(f27,plain,(
% 1.01/0.96    ( ! [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0) & v3_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.01/0.96    introduced(choice_axiom,[])).
% 1.01/0.96  
% 1.01/0.96  fof(f26,plain,(
% 1.01/0.96    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.01/0.96    introduced(choice_axiom,[])).
% 1.01/0.96  
% 1.01/0.96  fof(f28,plain,(
% 1.01/0.96    (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.01/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f27,f26])).
% 1.01/0.96  
% 1.01/0.96  fof(f43,plain,(
% 1.01/0.96    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.01/0.96    inference(cnf_transformation,[],[f28])).
% 1.01/0.96  
% 1.01/0.96  fof(f8,axiom,(
% 1.01/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.01/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/0.96  
% 1.01/0.96  fof(f18,plain,(
% 1.01/0.96    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.01/0.96    inference(ennf_transformation,[],[f8])).
% 1.01/0.96  
% 1.01/0.96  fof(f25,plain,(
% 1.01/0.96    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.01/0.96    inference(nnf_transformation,[],[f18])).
% 1.01/0.96  
% 1.01/0.96  fof(f40,plain,(
% 1.01/0.96    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.01/0.96    inference(cnf_transformation,[],[f25])).
% 1.01/0.96  
% 1.01/0.96  fof(f42,plain,(
% 1.01/0.96    l1_pre_topc(sK0)),
% 1.01/0.96    inference(cnf_transformation,[],[f28])).
% 1.01/0.96  
% 1.01/0.96  fof(f6,axiom,(
% 1.01/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 1.01/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/0.96  
% 1.01/0.96  fof(f15,plain,(
% 1.01/0.96    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.01/0.96    inference(ennf_transformation,[],[f6])).
% 1.01/0.96  
% 1.01/0.96  fof(f24,plain,(
% 1.01/0.96    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.01/0.96    inference(nnf_transformation,[],[f15])).
% 1.01/0.96  
% 1.01/0.96  fof(f37,plain,(
% 1.01/0.96    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.01/0.96    inference(cnf_transformation,[],[f24])).
% 1.01/0.96  
% 1.01/0.96  fof(f44,plain,(
% 1.01/0.96    v3_tops_1(sK1,sK0)),
% 1.01/0.96    inference(cnf_transformation,[],[f28])).
% 1.01/0.96  
% 1.01/0.96  fof(f3,axiom,(
% 1.01/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.01/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/0.96  
% 1.01/0.96  fof(f11,plain,(
% 1.01/0.96    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.01/0.96    inference(ennf_transformation,[],[f3])).
% 1.01/0.96  
% 1.01/0.96  fof(f12,plain,(
% 1.01/0.96    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.01/0.96    inference(flattening,[],[f11])).
% 1.01/0.96  
% 1.01/0.96  fof(f33,plain,(
% 1.01/0.96    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.01/0.96    inference(cnf_transformation,[],[f12])).
% 1.01/0.96  
% 1.01/0.96  fof(f7,axiom,(
% 1.01/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.01/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/0.96  
% 1.01/0.96  fof(f16,plain,(
% 1.01/0.96    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.01/0.96    inference(ennf_transformation,[],[f7])).
% 1.01/0.96  
% 1.01/0.96  fof(f17,plain,(
% 1.01/0.96    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.01/0.96    inference(flattening,[],[f16])).
% 1.01/0.96  
% 1.01/0.96  fof(f39,plain,(
% 1.01/0.96    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.01/0.96    inference(cnf_transformation,[],[f17])).
% 1.01/0.96  
% 1.01/0.96  fof(f4,axiom,(
% 1.01/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.01/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/0.96  
% 1.01/0.96  fof(f13,plain,(
% 1.01/0.96    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.01/0.96    inference(ennf_transformation,[],[f4])).
% 1.01/0.96  
% 1.01/0.96  fof(f34,plain,(
% 1.01/0.96    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.01/0.96    inference(cnf_transformation,[],[f13])).
% 1.01/0.96  
% 1.01/0.96  fof(f2,axiom,(
% 1.01/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.01/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/0.96  
% 1.01/0.96  fof(f32,plain,(
% 1.01/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.01/0.96    inference(cnf_transformation,[],[f2])).
% 1.01/0.96  
% 1.01/0.96  fof(f1,axiom,(
% 1.01/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.01/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/0.96  
% 1.01/0.96  fof(f21,plain,(
% 1.01/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.01/0.96    inference(nnf_transformation,[],[f1])).
% 1.01/0.96  
% 1.01/0.96  fof(f22,plain,(
% 1.01/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.01/0.96    inference(flattening,[],[f21])).
% 1.01/0.96  
% 1.01/0.96  fof(f31,plain,(
% 1.01/0.96    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.01/0.96    inference(cnf_transformation,[],[f22])).
% 1.01/0.96  
% 1.01/0.96  fof(f41,plain,(
% 1.01/0.96    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.01/0.96    inference(cnf_transformation,[],[f25])).
% 1.01/0.96  
% 1.01/0.96  fof(f5,axiom,(
% 1.01/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.01/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/0.96  
% 1.01/0.96  fof(f14,plain,(
% 1.01/0.96    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.01/0.96    inference(ennf_transformation,[],[f5])).
% 1.01/0.96  
% 1.01/0.96  fof(f23,plain,(
% 1.01/0.96    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.01/0.96    inference(nnf_transformation,[],[f14])).
% 1.01/0.96  
% 1.01/0.96  fof(f35,plain,(
% 1.01/0.96    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.01/0.96    inference(cnf_transformation,[],[f23])).
% 1.01/0.96  
% 1.01/0.96  fof(f45,plain,(
% 1.01/0.96    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.01/0.96    inference(cnf_transformation,[],[f28])).
% 1.01/0.96  
% 1.01/0.96  cnf(c_15,negated_conjecture,
% 1.01/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.01/0.96      inference(cnf_transformation,[],[f43]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_634,plain,
% 1.01/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.01/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_12,plain,
% 1.01/0.96      ( ~ v2_tops_1(X0,X1)
% 1.01/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | ~ l1_pre_topc(X1)
% 1.01/0.96      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 1.01/0.96      inference(cnf_transformation,[],[f40]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_16,negated_conjecture,
% 1.01/0.96      ( l1_pre_topc(sK0) ),
% 1.01/0.96      inference(cnf_transformation,[],[f42]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_225,plain,
% 1.01/0.96      ( ~ v2_tops_1(X0,X1)
% 1.01/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | k1_tops_1(X1,X0) = k1_xboole_0
% 1.01/0.96      | sK0 != X1 ),
% 1.01/0.96      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_226,plain,
% 1.01/0.96      ( ~ v2_tops_1(X0,sK0)
% 1.01/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 1.01/0.96      inference(unflattening,[status(thm)],[c_225]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_9,plain,
% 1.01/0.96      ( ~ v3_tops_1(X0,X1)
% 1.01/0.96      | v2_tops_1(k2_pre_topc(X1,X0),X1)
% 1.01/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | ~ l1_pre_topc(X1) ),
% 1.01/0.96      inference(cnf_transformation,[],[f37]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_14,negated_conjecture,
% 1.01/0.96      ( v3_tops_1(sK1,sK0) ),
% 1.01/0.96      inference(cnf_transformation,[],[f44]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_212,plain,
% 1.01/0.96      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 1.01/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.01/0.96      | ~ l1_pre_topc(X0)
% 1.01/0.96      | sK1 != X1
% 1.01/0.96      | sK0 != X0 ),
% 1.01/0.96      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_213,plain,
% 1.01/0.96      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 1.01/0.96      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | ~ l1_pre_topc(sK0) ),
% 1.01/0.96      inference(unflattening,[status(thm)],[c_212]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_215,plain,
% 1.01/0.96      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
% 1.01/0.96      inference(global_propositional_subsumption,
% 1.01/0.96                [status(thm)],
% 1.01/0.96                [c_213,c_16,c_15]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_331,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | k1_tops_1(sK0,X0) = k1_xboole_0
% 1.01/0.96      | k2_pre_topc(sK0,sK1) != X0
% 1.01/0.96      | sK0 != sK0 ),
% 1.01/0.96      inference(resolution_lifted,[status(thm)],[c_226,c_215]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_332,plain,
% 1.01/0.96      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 1.01/0.96      inference(unflattening,[status(thm)],[c_331]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_629,plain,
% 1.01/0.96      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0
% 1.01/0.96      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.01/0.96      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_4,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | ~ l1_pre_topc(X1) ),
% 1.01/0.96      inference(cnf_transformation,[],[f33]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_285,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | sK0 != X1 ),
% 1.01/0.96      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_286,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.01/0.96      inference(unflattening,[status(thm)],[c_285]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_702,plain,
% 1.01/0.96      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.01/0.96      inference(instantiation,[status(thm)],[c_286]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_817,plain,
% 1.01/0.96      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 1.01/0.96      inference(global_propositional_subsumption,
% 1.01/0.96                [status(thm)],
% 1.01/0.96                [c_629,c_15,c_332,c_702]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_10,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | ~ r1_tarski(X0,X2)
% 1.01/0.96      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 1.01/0.96      | ~ l1_pre_topc(X1) ),
% 1.01/0.96      inference(cnf_transformation,[],[f39]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_255,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | ~ r1_tarski(X0,X2)
% 1.01/0.96      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 1.01/0.96      | sK0 != X1 ),
% 1.01/0.96      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_256,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | ~ r1_tarski(X0,X1)
% 1.01/0.96      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 1.01/0.96      inference(unflattening,[status(thm)],[c_255]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_633,plain,
% 1.01/0.96      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.01/0.96      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.01/0.96      | r1_tarski(X0,X1) != iProver_top
% 1.01/0.96      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 1.01/0.96      inference(predicate_to_equality,[status(thm)],[c_256]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_821,plain,
% 1.01/0.96      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.01/0.96      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.01/0.96      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 1.01/0.96      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
% 1.01/0.96      inference(superposition,[status(thm)],[c_817,c_633]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_18,plain,
% 1.01/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.01/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_703,plain,
% 1.01/0.96      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 1.01/0.96      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.01/0.96      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_1287,plain,
% 1.01/0.96      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.01/0.96      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 1.01/0.96      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
% 1.01/0.96      inference(global_propositional_subsumption,
% 1.01/0.96                [status(thm)],
% 1.01/0.96                [c_821,c_18,c_703]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_1296,plain,
% 1.01/0.96      ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) = iProver_top
% 1.01/0.96      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 1.01/0.96      inference(superposition,[status(thm)],[c_634,c_1287]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_5,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 1.01/0.96      | ~ l1_pre_topc(X1) ),
% 1.01/0.96      inference(cnf_transformation,[],[f34]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_273,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 1.01/0.96      | sK0 != X1 ),
% 1.01/0.96      inference(resolution_lifted,[status(thm)],[c_5,c_16]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_274,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 1.01/0.96      inference(unflattening,[status(thm)],[c_273]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_705,plain,
% 1.01/0.96      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 1.01/0.96      inference(instantiation,[status(thm)],[c_274]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_706,plain,
% 1.01/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.01/0.96      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 1.01/0.96      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_1313,plain,
% 1.01/0.96      ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 1.01/0.96      inference(global_propositional_subsumption,
% 1.01/0.96                [status(thm)],
% 1.01/0.96                [c_1296,c_18,c_706]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_3,plain,
% 1.01/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 1.01/0.96      inference(cnf_transformation,[],[f32]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_635,plain,
% 1.01/0.96      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.01/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_0,plain,
% 1.01/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.01/0.96      inference(cnf_transformation,[],[f31]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_637,plain,
% 1.01/0.96      ( X0 = X1
% 1.01/0.96      | r1_tarski(X0,X1) != iProver_top
% 1.01/0.96      | r1_tarski(X1,X0) != iProver_top ),
% 1.01/0.96      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_1050,plain,
% 1.01/0.96      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.01/0.96      inference(superposition,[status(thm)],[c_635,c_637]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_1319,plain,
% 1.01/0.96      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 1.01/0.96      inference(superposition,[status(thm)],[c_1313,c_1050]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_11,plain,
% 1.01/0.96      ( v2_tops_1(X0,X1)
% 1.01/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | ~ l1_pre_topc(X1)
% 1.01/0.96      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 1.01/0.96      inference(cnf_transformation,[],[f41]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_240,plain,
% 1.01/0.96      ( v2_tops_1(X0,X1)
% 1.01/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | k1_tops_1(X1,X0) != k1_xboole_0
% 1.01/0.96      | sK0 != X1 ),
% 1.01/0.96      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_241,plain,
% 1.01/0.96      ( v2_tops_1(X0,sK0)
% 1.01/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 1.01/0.96      inference(unflattening,[status(thm)],[c_240]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_7,plain,
% 1.01/0.96      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 1.01/0.96      | ~ v2_tops_1(X1,X0)
% 1.01/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.01/0.96      | ~ l1_pre_topc(X0) ),
% 1.01/0.96      inference(cnf_transformation,[],[f35]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_13,negated_conjecture,
% 1.01/0.96      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 1.01/0.96      inference(cnf_transformation,[],[f45]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_186,plain,
% 1.01/0.96      ( ~ v2_tops_1(X0,X1)
% 1.01/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.01/0.96      | ~ l1_pre_topc(X1)
% 1.01/0.96      | k3_subset_1(u1_struct_0(X1),X0) != k3_subset_1(u1_struct_0(sK0),sK1)
% 1.01/0.96      | sK0 != X1 ),
% 1.01/0.96      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_187,plain,
% 1.01/0.96      ( ~ v2_tops_1(X0,sK0)
% 1.01/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | ~ l1_pre_topc(sK0)
% 1.01/0.96      | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
% 1.01/0.96      inference(unflattening,[status(thm)],[c_186]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_191,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | ~ v2_tops_1(X0,sK0)
% 1.01/0.96      | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
% 1.01/0.96      inference(global_propositional_subsumption,
% 1.01/0.96                [status(thm)],
% 1.01/0.96                [c_187,c_16]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_192,plain,
% 1.01/0.96      ( ~ v2_tops_1(X0,sK0)
% 1.01/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
% 1.01/0.96      inference(renaming,[status(thm)],[c_191]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_317,plain,
% 1.01/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.01/0.96      | k1_tops_1(sK0,X0) != k1_xboole_0
% 1.01/0.96      | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
% 1.01/0.96      inference(resolution,[status(thm)],[c_241,c_192]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_630,plain,
% 1.01/0.96      ( k1_tops_1(sK0,X0) != k1_xboole_0
% 1.01/0.96      | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1)
% 1.01/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.01/0.96      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(c_999,plain,
% 1.01/0.96      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 1.01/0.96      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.01/0.96      inference(equality_resolution,[status(thm)],[c_630]) ).
% 1.01/0.96  
% 1.01/0.96  cnf(contradiction,plain,
% 1.01/0.96      ( $false ),
% 1.01/0.96      inference(minisat,[status(thm)],[c_1319,c_999,c_18]) ).
% 1.01/0.96  
% 1.01/0.96  
% 1.01/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 1.01/0.96  
% 1.01/0.96  ------                               Statistics
% 1.01/0.96  
% 1.01/0.96  ------ General
% 1.01/0.96  
% 1.01/0.96  abstr_ref_over_cycles:                  0
% 1.01/0.96  abstr_ref_under_cycles:                 0
% 1.01/0.96  gc_basic_clause_elim:                   0
% 1.01/0.96  forced_gc_time:                         0
% 1.01/0.96  parsing_time:                           0.008
% 1.01/0.96  unif_index_cands_time:                  0.
% 1.01/0.96  unif_index_add_time:                    0.
% 1.01/0.96  orderings_time:                         0.
% 1.01/0.96  out_proof_time:                         0.009
% 1.01/0.96  total_time:                             0.068
% 1.01/0.96  num_of_symbols:                         45
% 1.01/0.96  num_of_terms:                           1059
% 1.01/0.96  
% 1.01/0.96  ------ Preprocessing
% 1.01/0.96  
% 1.01/0.96  num_of_splits:                          0
% 1.01/0.96  num_of_split_atoms:                     0
% 1.01/0.96  num_of_reused_defs:                     0
% 1.01/0.96  num_eq_ax_congr_red:                    5
% 1.01/0.96  num_of_sem_filtered_clauses:            1
% 1.01/0.96  num_of_subtypes:                        0
% 1.01/0.96  monotx_restored_types:                  0
% 1.01/0.96  sat_num_of_epr_types:                   0
% 1.01/0.96  sat_num_of_non_cyclic_types:            0
% 1.01/0.96  sat_guarded_non_collapsed_types:        0
% 1.01/0.96  num_pure_diseq_elim:                    0
% 1.01/0.96  simp_replaced_by:                       0
% 1.01/0.96  res_preprocessed:                       65
% 1.01/0.96  prep_upred:                             0
% 1.01/0.96  prep_unflattend:                        10
% 1.01/0.96  smt_new_axioms:                         0
% 1.01/0.96  pred_elim_cands:                        2
% 1.01/0.96  pred_elim:                              4
% 1.01/0.96  pred_elim_cl:                           6
% 1.01/0.96  pred_elim_cycles:                       6
% 1.01/0.96  merged_defs:                            0
% 1.01/0.96  merged_defs_ncl:                        0
% 1.01/0.96  bin_hyper_res:                          0
% 1.01/0.96  prep_cycles:                            4
% 1.01/0.96  pred_elim_time:                         0.003
% 1.01/0.96  splitting_time:                         0.
% 1.01/0.96  sem_filter_time:                        0.
% 1.01/0.96  monotx_time:                            0.
% 1.01/0.96  subtype_inf_time:                       0.
% 1.01/0.96  
% 1.01/0.96  ------ Problem properties
% 1.01/0.96  
% 1.01/0.96  clauses:                                10
% 1.01/0.96  conjectures:                            1
% 1.01/0.96  epr:                                    3
% 1.01/0.96  horn:                                   10
% 1.01/0.96  ground:                                 3
% 1.01/0.96  unary:                                  3
% 1.01/0.96  binary:                                 4
% 1.01/0.96  lits:                                   21
% 1.01/0.96  lits_eq:                                5
% 1.01/0.96  fd_pure:                                0
% 1.01/0.96  fd_pseudo:                              0
% 1.01/0.96  fd_cond:                                0
% 1.01/0.96  fd_pseudo_cond:                         1
% 1.01/0.96  ac_symbols:                             0
% 1.01/0.96  
% 1.01/0.96  ------ Propositional Solver
% 1.01/0.96  
% 1.01/0.96  prop_solver_calls:                      26
% 1.01/0.96  prop_fast_solver_calls:                 397
% 1.01/0.96  smt_solver_calls:                       0
% 1.01/0.96  smt_fast_solver_calls:                  0
% 1.01/0.96  prop_num_of_clauses:                    441
% 1.01/0.96  prop_preprocess_simplified:             2048
% 1.01/0.96  prop_fo_subsumed:                       9
% 1.01/0.96  prop_solver_time:                       0.
% 1.01/0.96  smt_solver_time:                        0.
% 1.01/0.96  smt_fast_solver_time:                   0.
% 1.01/0.96  prop_fast_solver_time:                  0.
% 1.01/0.96  prop_unsat_core_time:                   0.
% 1.01/0.96  
% 1.01/0.96  ------ QBF
% 1.01/0.96  
% 1.01/0.96  qbf_q_res:                              0
% 1.01/0.96  qbf_num_tautologies:                    0
% 1.01/0.96  qbf_prep_cycles:                        0
% 1.01/0.96  
% 1.01/0.96  ------ BMC1
% 1.01/0.96  
% 1.01/0.96  bmc1_current_bound:                     -1
% 1.01/0.96  bmc1_last_solved_bound:                 -1
% 1.01/0.96  bmc1_unsat_core_size:                   -1
% 1.01/0.96  bmc1_unsat_core_parents_size:           -1
% 1.01/0.96  bmc1_merge_next_fun:                    0
% 1.01/0.96  bmc1_unsat_core_clauses_time:           0.
% 1.01/0.96  
% 1.01/0.96  ------ Instantiation
% 1.01/0.96  
% 1.01/0.96  inst_num_of_clauses:                    129
% 1.01/0.96  inst_num_in_passive:                    13
% 1.01/0.96  inst_num_in_active:                     76
% 1.01/0.96  inst_num_in_unprocessed:                41
% 1.01/0.96  inst_num_of_loops:                      80
% 1.01/0.96  inst_num_of_learning_restarts:          0
% 1.01/0.96  inst_num_moves_active_passive:          2
% 1.01/0.96  inst_lit_activity:                      0
% 1.01/0.96  inst_lit_activity_moves:                0
% 1.01/0.96  inst_num_tautologies:                   0
% 1.01/0.96  inst_num_prop_implied:                  0
% 1.01/0.96  inst_num_existing_simplified:           0
% 1.01/0.96  inst_num_eq_res_simplified:             0
% 1.01/0.96  inst_num_child_elim:                    0
% 1.01/0.96  inst_num_of_dismatching_blockings:      6
% 1.01/0.96  inst_num_of_non_proper_insts:           101
% 1.01/0.96  inst_num_of_duplicates:                 0
% 1.01/0.96  inst_inst_num_from_inst_to_res:         0
% 1.01/0.96  inst_dismatching_checking_time:         0.
% 1.01/0.96  
% 1.01/0.96  ------ Resolution
% 1.01/0.96  
% 1.01/0.96  res_num_of_clauses:                     0
% 1.01/0.96  res_num_in_passive:                     0
% 1.01/0.96  res_num_in_active:                      0
% 1.01/0.96  res_num_of_loops:                       69
% 1.01/0.96  res_forward_subset_subsumed:            9
% 1.01/0.96  res_backward_subset_subsumed:           2
% 1.01/0.96  res_forward_subsumed:                   0
% 1.01/0.96  res_backward_subsumed:                  0
% 1.01/0.96  res_forward_subsumption_resolution:     0
% 1.01/0.96  res_backward_subsumption_resolution:    0
% 1.01/0.96  res_clause_to_clause_subsumption:       68
% 1.01/0.96  res_orphan_elimination:                 0
% 1.01/0.96  res_tautology_del:                      11
% 1.01/0.96  res_num_eq_res_simplified:              0
% 1.01/0.96  res_num_sel_changes:                    0
% 1.01/0.96  res_moves_from_active_to_pass:          0
% 1.01/0.96  
% 1.01/0.96  ------ Superposition
% 1.01/0.96  
% 1.01/0.96  sup_time_total:                         0.
% 1.01/0.96  sup_time_generating:                    0.
% 1.01/0.96  sup_time_sim_full:                      0.
% 1.01/0.96  sup_time_sim_immed:                     0.
% 1.01/0.96  
% 1.01/0.96  sup_num_of_clauses:                     22
% 1.01/0.96  sup_num_in_active:                      16
% 1.01/0.96  sup_num_in_passive:                     6
% 1.01/0.96  sup_num_of_loops:                       15
% 1.01/0.96  sup_fw_superposition:                   10
% 1.01/0.96  sup_bw_superposition:                   5
% 1.01/0.96  sup_immediate_simplified:               0
% 1.01/0.96  sup_given_eliminated:                   1
% 1.01/0.96  comparisons_done:                       0
% 1.01/0.96  comparisons_avoided:                    0
% 1.01/0.96  
% 1.01/0.96  ------ Simplifications
% 1.01/0.96  
% 1.01/0.96  
% 1.01/0.96  sim_fw_subset_subsumed:                 0
% 1.01/0.96  sim_bw_subset_subsumed:                 0
% 1.01/0.96  sim_fw_subsumed:                        2
% 1.01/0.96  sim_bw_subsumed:                        0
% 1.01/0.96  sim_fw_subsumption_res:                 0
% 1.01/0.96  sim_bw_subsumption_res:                 0
% 1.01/0.96  sim_tautology_del:                      0
% 1.01/0.96  sim_eq_tautology_del:                   1
% 1.01/0.96  sim_eq_res_simp:                        0
% 1.01/0.96  sim_fw_demodulated:                     0
% 1.01/0.96  sim_bw_demodulated:                     1
% 1.01/0.96  sim_light_normalised:                   0
% 1.01/0.96  sim_joinable_taut:                      0
% 1.01/0.96  sim_joinable_simp:                      0
% 1.01/0.96  sim_ac_normalised:                      0
% 1.01/0.96  sim_smt_subsumption:                    0
% 1.01/0.96  
%------------------------------------------------------------------------------
