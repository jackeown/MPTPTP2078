%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:28 EST 2020

% Result     : Theorem 39.33s
% Output     : CNFRefutation 39.33s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 451 expanded)
%              Number of clauses        :   91 ( 195 expanded)
%              Number of leaves         :   19 (  91 expanded)
%              Depth                    :   19
%              Number of atoms          :  376 (1377 expanded)
%              Number of equality atoms :  140 ( 340 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,sK3)),k3_subset_1(X0,X1))
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2))
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f34,f33])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f58,plain,(
    ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1222,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1228,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1872,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1228])).

cnf(c_18,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_31,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2128,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1872,c_31])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1232,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2132,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_1232])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1241,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2212,plain,
    ( k2_xboole_0(sK2,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2132,c_1241])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1223,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1871,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_1228])).

cnf(c_2121,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1871,c_31])).

cnf(c_2125,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2121,c_1232])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1242,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1238,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2354,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1238])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1240,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6041,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(k2_xboole_0(X2,X0),X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2354,c_1240])).

cnf(c_104864,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X2) = X2
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6041,c_1241])).

cnf(c_123730,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK3),X0),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2125,c_104864])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1236,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1237,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2018,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1237])).

cnf(c_125862,plain,
    ( r1_tarski(k2_xboole_0(X0,sK3),k2_xboole_0(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_123730,c_2018])).

cnf(c_131396,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(X0,sK1)) = k2_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_125862,c_1241])).

cnf(c_132342,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK1) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_2212,c_131396])).

cnf(c_132650,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_132342,c_2212])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1233,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1229,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2276,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_1229])).

cnf(c_182,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_183,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_370,plain,
    ( m1_subset_1(X0,X1)
    | ~ r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | X0 != X2
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_183,c_15])).

cnf(c_371,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_381,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_371,c_18])).

cnf(c_384,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_7250,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2276,c_384])).

cnf(c_7251,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7250])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1227,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7257,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7251,c_1227])).

cnf(c_64248,plain,
    ( k3_subset_1(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1236,c_7257])).

cnf(c_133392,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK3),sK1),k2_xboole_0(sK2,sK3)) = k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_132650,c_64248])).

cnf(c_133462,plain,
    ( k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_133392,c_132650])).

cnf(c_50617,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1839,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_22560,plain,
    ( r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_726,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1302,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k3_subset_1(sK1,sK2))
    | X2 != X0
    | k3_subset_1(sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1426,plain,
    ( r1_tarski(X0,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(X1,k4_xboole_0(sK1,sK2))
    | X0 != X1
    | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_1721,plain,
    ( r1_tarski(X0,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(sK1,sK2))
    | X0 != k4_xboole_0(X1,X2)
    | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1426])).

cnf(c_3541,plain,
    ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(sK1,sK2))
    | k3_subset_1(X0,X1) != k4_xboole_0(X0,X1)
    | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1721])).

cnf(c_9401,plain,
    ( r1_tarski(k3_subset_1(X0,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
    | k3_subset_1(X0,k2_xboole_0(sK2,sK3)) != k4_xboole_0(X0,k2_xboole_0(sK2,sK3))
    | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3541])).

cnf(c_9408,plain,
    ( r1_tarski(k3_subset_1(sK1,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
    | k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) != k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_9401])).

cnf(c_1277,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != X0
    | k3_subset_1(sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1322,plain,
    ( ~ r1_tarski(X0,k3_subset_1(sK1,sK2))
    | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != X0
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1277])).

cnf(c_1916,plain,
    ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(sK1,sK2))
    | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(X0,X1)
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_6235,plain,
    ( ~ r1_tarski(k3_subset_1(X0,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
    | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(X0,k2_xboole_0(sK2,sK3))
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_6247,plain,
    ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k3_subset_1(sK1,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(sK1,k2_xboole_0(sK2,sK3))
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_6235])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1225,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3475,plain,
    ( k4_subset_1(sK1,sK2,X0) = k2_xboole_0(sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1225])).

cnf(c_3674,plain,
    ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1223,c_3475])).

cnf(c_731,plain,
    ( X0 != X1
    | X2 != X3
    | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_1969,plain,
    ( k4_subset_1(sK1,sK2,sK3) != X0
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(X1,X0)
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_3466,plain,
    ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(X0,k2_xboole_0(sK2,sK3))
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_3467,plain,
    ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(sK1,k2_xboole_0(sK2,sK3))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3466])).

cnf(c_724,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1388,plain,
    ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_1381,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_76,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_72,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_133462,c_50617,c_22560,c_9408,c_6247,c_3674,c_3467,c_1388,c_1381,c_76,c_72,c_20,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:58:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 39.33/5.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.33/5.50  
% 39.33/5.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.33/5.50  
% 39.33/5.50  ------  iProver source info
% 39.33/5.50  
% 39.33/5.50  git: date: 2020-06-30 10:37:57 +0100
% 39.33/5.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.33/5.50  git: non_committed_changes: false
% 39.33/5.50  git: last_make_outside_of_git: false
% 39.33/5.50  
% 39.33/5.50  ------ 
% 39.33/5.50  
% 39.33/5.50  ------ Input Options
% 39.33/5.50  
% 39.33/5.50  --out_options                           all
% 39.33/5.50  --tptp_safe_out                         true
% 39.33/5.50  --problem_path                          ""
% 39.33/5.50  --include_path                          ""
% 39.33/5.50  --clausifier                            res/vclausify_rel
% 39.33/5.50  --clausifier_options                    ""
% 39.33/5.50  --stdin                                 false
% 39.33/5.50  --stats_out                             all
% 39.33/5.50  
% 39.33/5.50  ------ General Options
% 39.33/5.50  
% 39.33/5.50  --fof                                   false
% 39.33/5.50  --time_out_real                         305.
% 39.33/5.50  --time_out_virtual                      -1.
% 39.33/5.50  --symbol_type_check                     false
% 39.33/5.50  --clausify_out                          false
% 39.33/5.50  --sig_cnt_out                           false
% 39.33/5.50  --trig_cnt_out                          false
% 39.33/5.50  --trig_cnt_out_tolerance                1.
% 39.33/5.50  --trig_cnt_out_sk_spl                   false
% 39.33/5.50  --abstr_cl_out                          false
% 39.33/5.50  
% 39.33/5.50  ------ Global Options
% 39.33/5.50  
% 39.33/5.50  --schedule                              default
% 39.33/5.50  --add_important_lit                     false
% 39.33/5.50  --prop_solver_per_cl                    1000
% 39.33/5.50  --min_unsat_core                        false
% 39.33/5.50  --soft_assumptions                      false
% 39.33/5.50  --soft_lemma_size                       3
% 39.33/5.50  --prop_impl_unit_size                   0
% 39.33/5.50  --prop_impl_unit                        []
% 39.33/5.50  --share_sel_clauses                     true
% 39.33/5.50  --reset_solvers                         false
% 39.33/5.50  --bc_imp_inh                            [conj_cone]
% 39.33/5.50  --conj_cone_tolerance                   3.
% 39.33/5.50  --extra_neg_conj                        none
% 39.33/5.50  --large_theory_mode                     true
% 39.33/5.50  --prolific_symb_bound                   200
% 39.33/5.50  --lt_threshold                          2000
% 39.33/5.50  --clause_weak_htbl                      true
% 39.33/5.50  --gc_record_bc_elim                     false
% 39.33/5.50  
% 39.33/5.50  ------ Preprocessing Options
% 39.33/5.50  
% 39.33/5.50  --preprocessing_flag                    true
% 39.33/5.50  --time_out_prep_mult                    0.1
% 39.33/5.50  --splitting_mode                        input
% 39.33/5.50  --splitting_grd                         true
% 39.33/5.50  --splitting_cvd                         false
% 39.33/5.50  --splitting_cvd_svl                     false
% 39.33/5.50  --splitting_nvd                         32
% 39.33/5.50  --sub_typing                            true
% 39.33/5.50  --prep_gs_sim                           true
% 39.33/5.50  --prep_unflatten                        true
% 39.33/5.50  --prep_res_sim                          true
% 39.33/5.50  --prep_upred                            true
% 39.33/5.50  --prep_sem_filter                       exhaustive
% 39.33/5.50  --prep_sem_filter_out                   false
% 39.33/5.50  --pred_elim                             true
% 39.33/5.50  --res_sim_input                         true
% 39.33/5.50  --eq_ax_congr_red                       true
% 39.33/5.50  --pure_diseq_elim                       true
% 39.33/5.50  --brand_transform                       false
% 39.33/5.50  --non_eq_to_eq                          false
% 39.33/5.50  --prep_def_merge                        true
% 39.33/5.50  --prep_def_merge_prop_impl              false
% 39.33/5.50  --prep_def_merge_mbd                    true
% 39.33/5.50  --prep_def_merge_tr_red                 false
% 39.33/5.50  --prep_def_merge_tr_cl                  false
% 39.33/5.50  --smt_preprocessing                     true
% 39.33/5.50  --smt_ac_axioms                         fast
% 39.33/5.50  --preprocessed_out                      false
% 39.33/5.50  --preprocessed_stats                    false
% 39.33/5.50  
% 39.33/5.50  ------ Abstraction refinement Options
% 39.33/5.50  
% 39.33/5.50  --abstr_ref                             []
% 39.33/5.50  --abstr_ref_prep                        false
% 39.33/5.50  --abstr_ref_until_sat                   false
% 39.33/5.50  --abstr_ref_sig_restrict                funpre
% 39.33/5.50  --abstr_ref_af_restrict_to_split_sk     false
% 39.33/5.50  --abstr_ref_under                       []
% 39.33/5.50  
% 39.33/5.50  ------ SAT Options
% 39.33/5.50  
% 39.33/5.50  --sat_mode                              false
% 39.33/5.50  --sat_fm_restart_options                ""
% 39.33/5.50  --sat_gr_def                            false
% 39.33/5.50  --sat_epr_types                         true
% 39.33/5.50  --sat_non_cyclic_types                  false
% 39.33/5.50  --sat_finite_models                     false
% 39.33/5.50  --sat_fm_lemmas                         false
% 39.33/5.50  --sat_fm_prep                           false
% 39.33/5.50  --sat_fm_uc_incr                        true
% 39.33/5.50  --sat_out_model                         small
% 39.33/5.50  --sat_out_clauses                       false
% 39.33/5.50  
% 39.33/5.50  ------ QBF Options
% 39.33/5.50  
% 39.33/5.50  --qbf_mode                              false
% 39.33/5.50  --qbf_elim_univ                         false
% 39.33/5.50  --qbf_dom_inst                          none
% 39.33/5.50  --qbf_dom_pre_inst                      false
% 39.33/5.50  --qbf_sk_in                             false
% 39.33/5.50  --qbf_pred_elim                         true
% 39.33/5.50  --qbf_split                             512
% 39.33/5.50  
% 39.33/5.50  ------ BMC1 Options
% 39.33/5.50  
% 39.33/5.50  --bmc1_incremental                      false
% 39.33/5.50  --bmc1_axioms                           reachable_all
% 39.33/5.50  --bmc1_min_bound                        0
% 39.33/5.50  --bmc1_max_bound                        -1
% 39.33/5.50  --bmc1_max_bound_default                -1
% 39.33/5.50  --bmc1_symbol_reachability              true
% 39.33/5.50  --bmc1_property_lemmas                  false
% 39.33/5.50  --bmc1_k_induction                      false
% 39.33/5.50  --bmc1_non_equiv_states                 false
% 39.33/5.50  --bmc1_deadlock                         false
% 39.33/5.50  --bmc1_ucm                              false
% 39.33/5.50  --bmc1_add_unsat_core                   none
% 39.33/5.50  --bmc1_unsat_core_children              false
% 39.33/5.50  --bmc1_unsat_core_extrapolate_axioms    false
% 39.33/5.50  --bmc1_out_stat                         full
% 39.33/5.50  --bmc1_ground_init                      false
% 39.33/5.50  --bmc1_pre_inst_next_state              false
% 39.33/5.50  --bmc1_pre_inst_state                   false
% 39.33/5.50  --bmc1_pre_inst_reach_state             false
% 39.33/5.50  --bmc1_out_unsat_core                   false
% 39.33/5.50  --bmc1_aig_witness_out                  false
% 39.33/5.50  --bmc1_verbose                          false
% 39.33/5.50  --bmc1_dump_clauses_tptp                false
% 39.33/5.50  --bmc1_dump_unsat_core_tptp             false
% 39.33/5.50  --bmc1_dump_file                        -
% 39.33/5.50  --bmc1_ucm_expand_uc_limit              128
% 39.33/5.50  --bmc1_ucm_n_expand_iterations          6
% 39.33/5.50  --bmc1_ucm_extend_mode                  1
% 39.33/5.50  --bmc1_ucm_init_mode                    2
% 39.33/5.50  --bmc1_ucm_cone_mode                    none
% 39.33/5.50  --bmc1_ucm_reduced_relation_type        0
% 39.33/5.50  --bmc1_ucm_relax_model                  4
% 39.33/5.50  --bmc1_ucm_full_tr_after_sat            true
% 39.33/5.50  --bmc1_ucm_expand_neg_assumptions       false
% 39.33/5.50  --bmc1_ucm_layered_model                none
% 39.33/5.50  --bmc1_ucm_max_lemma_size               10
% 39.33/5.50  
% 39.33/5.50  ------ AIG Options
% 39.33/5.50  
% 39.33/5.50  --aig_mode                              false
% 39.33/5.50  
% 39.33/5.50  ------ Instantiation Options
% 39.33/5.50  
% 39.33/5.50  --instantiation_flag                    true
% 39.33/5.50  --inst_sos_flag                         true
% 39.33/5.50  --inst_sos_phase                        true
% 39.33/5.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.33/5.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.33/5.50  --inst_lit_sel_side                     num_symb
% 39.33/5.50  --inst_solver_per_active                1400
% 39.33/5.50  --inst_solver_calls_frac                1.
% 39.33/5.50  --inst_passive_queue_type               priority_queues
% 39.33/5.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.33/5.50  --inst_passive_queues_freq              [25;2]
% 39.33/5.50  --inst_dismatching                      true
% 39.33/5.50  --inst_eager_unprocessed_to_passive     true
% 39.33/5.50  --inst_prop_sim_given                   true
% 39.33/5.50  --inst_prop_sim_new                     false
% 39.33/5.50  --inst_subs_new                         false
% 39.33/5.50  --inst_eq_res_simp                      false
% 39.33/5.50  --inst_subs_given                       false
% 39.33/5.50  --inst_orphan_elimination               true
% 39.33/5.50  --inst_learning_loop_flag               true
% 39.33/5.50  --inst_learning_start                   3000
% 39.33/5.50  --inst_learning_factor                  2
% 39.33/5.50  --inst_start_prop_sim_after_learn       3
% 39.33/5.50  --inst_sel_renew                        solver
% 39.33/5.50  --inst_lit_activity_flag                true
% 39.33/5.50  --inst_restr_to_given                   false
% 39.33/5.50  --inst_activity_threshold               500
% 39.33/5.50  --inst_out_proof                        true
% 39.33/5.50  
% 39.33/5.50  ------ Resolution Options
% 39.33/5.50  
% 39.33/5.50  --resolution_flag                       true
% 39.33/5.50  --res_lit_sel                           adaptive
% 39.33/5.50  --res_lit_sel_side                      none
% 39.33/5.50  --res_ordering                          kbo
% 39.33/5.50  --res_to_prop_solver                    active
% 39.33/5.50  --res_prop_simpl_new                    false
% 39.33/5.50  --res_prop_simpl_given                  true
% 39.33/5.50  --res_passive_queue_type                priority_queues
% 39.33/5.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.33/5.50  --res_passive_queues_freq               [15;5]
% 39.33/5.50  --res_forward_subs                      full
% 39.33/5.50  --res_backward_subs                     full
% 39.33/5.50  --res_forward_subs_resolution           true
% 39.33/5.50  --res_backward_subs_resolution          true
% 39.33/5.50  --res_orphan_elimination                true
% 39.33/5.50  --res_time_limit                        2.
% 39.33/5.50  --res_out_proof                         true
% 39.33/5.50  
% 39.33/5.50  ------ Superposition Options
% 39.33/5.50  
% 39.33/5.50  --superposition_flag                    true
% 39.33/5.50  --sup_passive_queue_type                priority_queues
% 39.33/5.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.33/5.50  --sup_passive_queues_freq               [8;1;4]
% 39.33/5.50  --demod_completeness_check              fast
% 39.33/5.50  --demod_use_ground                      true
% 39.33/5.50  --sup_to_prop_solver                    passive
% 39.33/5.50  --sup_prop_simpl_new                    true
% 39.33/5.50  --sup_prop_simpl_given                  true
% 39.33/5.50  --sup_fun_splitting                     true
% 39.33/5.50  --sup_smt_interval                      50000
% 39.33/5.50  
% 39.33/5.50  ------ Superposition Simplification Setup
% 39.33/5.50  
% 39.33/5.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.33/5.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.33/5.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.33/5.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.33/5.50  --sup_full_triv                         [TrivRules;PropSubs]
% 39.33/5.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.33/5.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.33/5.50  --sup_immed_triv                        [TrivRules]
% 39.33/5.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.33/5.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.33/5.50  --sup_immed_bw_main                     []
% 39.33/5.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.33/5.50  --sup_input_triv                        [Unflattening;TrivRules]
% 39.33/5.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.33/5.50  --sup_input_bw                          []
% 39.33/5.50  
% 39.33/5.50  ------ Combination Options
% 39.33/5.50  
% 39.33/5.50  --comb_res_mult                         3
% 39.33/5.50  --comb_sup_mult                         2
% 39.33/5.50  --comb_inst_mult                        10
% 39.33/5.50  
% 39.33/5.50  ------ Debug Options
% 39.33/5.50  
% 39.33/5.50  --dbg_backtrace                         false
% 39.33/5.50  --dbg_dump_prop_clauses                 false
% 39.33/5.50  --dbg_dump_prop_clauses_file            -
% 39.33/5.50  --dbg_out_stat                          false
% 39.33/5.50  ------ Parsing...
% 39.33/5.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.33/5.50  
% 39.33/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.33/5.50  
% 39.33/5.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.33/5.50  
% 39.33/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.33/5.50  ------ Proving...
% 39.33/5.50  ------ Problem Properties 
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  clauses                                 22
% 39.33/5.50  conjectures                             3
% 39.33/5.50  EPR                                     7
% 39.33/5.50  Horn                                    19
% 39.33/5.50  unary                                   6
% 39.33/5.50  binary                                  7
% 39.33/5.50  lits                                    47
% 39.33/5.50  lits eq                                 6
% 39.33/5.50  fd_pure                                 0
% 39.33/5.50  fd_pseudo                               0
% 39.33/5.50  fd_cond                                 0
% 39.33/5.50  fd_pseudo_cond                          3
% 39.33/5.50  AC symbols                              0
% 39.33/5.50  
% 39.33/5.50  ------ Schedule dynamic 5 is on 
% 39.33/5.50  
% 39.33/5.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  ------ 
% 39.33/5.50  Current options:
% 39.33/5.50  ------ 
% 39.33/5.50  
% 39.33/5.50  ------ Input Options
% 39.33/5.50  
% 39.33/5.50  --out_options                           all
% 39.33/5.50  --tptp_safe_out                         true
% 39.33/5.50  --problem_path                          ""
% 39.33/5.50  --include_path                          ""
% 39.33/5.50  --clausifier                            res/vclausify_rel
% 39.33/5.50  --clausifier_options                    ""
% 39.33/5.50  --stdin                                 false
% 39.33/5.50  --stats_out                             all
% 39.33/5.50  
% 39.33/5.50  ------ General Options
% 39.33/5.50  
% 39.33/5.50  --fof                                   false
% 39.33/5.50  --time_out_real                         305.
% 39.33/5.50  --time_out_virtual                      -1.
% 39.33/5.50  --symbol_type_check                     false
% 39.33/5.50  --clausify_out                          false
% 39.33/5.50  --sig_cnt_out                           false
% 39.33/5.50  --trig_cnt_out                          false
% 39.33/5.50  --trig_cnt_out_tolerance                1.
% 39.33/5.50  --trig_cnt_out_sk_spl                   false
% 39.33/5.50  --abstr_cl_out                          false
% 39.33/5.50  
% 39.33/5.50  ------ Global Options
% 39.33/5.50  
% 39.33/5.50  --schedule                              default
% 39.33/5.50  --add_important_lit                     false
% 39.33/5.50  --prop_solver_per_cl                    1000
% 39.33/5.50  --min_unsat_core                        false
% 39.33/5.50  --soft_assumptions                      false
% 39.33/5.50  --soft_lemma_size                       3
% 39.33/5.50  --prop_impl_unit_size                   0
% 39.33/5.50  --prop_impl_unit                        []
% 39.33/5.50  --share_sel_clauses                     true
% 39.33/5.50  --reset_solvers                         false
% 39.33/5.50  --bc_imp_inh                            [conj_cone]
% 39.33/5.50  --conj_cone_tolerance                   3.
% 39.33/5.50  --extra_neg_conj                        none
% 39.33/5.50  --large_theory_mode                     true
% 39.33/5.50  --prolific_symb_bound                   200
% 39.33/5.50  --lt_threshold                          2000
% 39.33/5.50  --clause_weak_htbl                      true
% 39.33/5.50  --gc_record_bc_elim                     false
% 39.33/5.50  
% 39.33/5.50  ------ Preprocessing Options
% 39.33/5.50  
% 39.33/5.50  --preprocessing_flag                    true
% 39.33/5.50  --time_out_prep_mult                    0.1
% 39.33/5.50  --splitting_mode                        input
% 39.33/5.50  --splitting_grd                         true
% 39.33/5.50  --splitting_cvd                         false
% 39.33/5.50  --splitting_cvd_svl                     false
% 39.33/5.50  --splitting_nvd                         32
% 39.33/5.50  --sub_typing                            true
% 39.33/5.50  --prep_gs_sim                           true
% 39.33/5.50  --prep_unflatten                        true
% 39.33/5.50  --prep_res_sim                          true
% 39.33/5.50  --prep_upred                            true
% 39.33/5.50  --prep_sem_filter                       exhaustive
% 39.33/5.50  --prep_sem_filter_out                   false
% 39.33/5.50  --pred_elim                             true
% 39.33/5.50  --res_sim_input                         true
% 39.33/5.50  --eq_ax_congr_red                       true
% 39.33/5.50  --pure_diseq_elim                       true
% 39.33/5.50  --brand_transform                       false
% 39.33/5.50  --non_eq_to_eq                          false
% 39.33/5.50  --prep_def_merge                        true
% 39.33/5.50  --prep_def_merge_prop_impl              false
% 39.33/5.50  --prep_def_merge_mbd                    true
% 39.33/5.50  --prep_def_merge_tr_red                 false
% 39.33/5.50  --prep_def_merge_tr_cl                  false
% 39.33/5.50  --smt_preprocessing                     true
% 39.33/5.50  --smt_ac_axioms                         fast
% 39.33/5.50  --preprocessed_out                      false
% 39.33/5.50  --preprocessed_stats                    false
% 39.33/5.50  
% 39.33/5.50  ------ Abstraction refinement Options
% 39.33/5.50  
% 39.33/5.50  --abstr_ref                             []
% 39.33/5.50  --abstr_ref_prep                        false
% 39.33/5.50  --abstr_ref_until_sat                   false
% 39.33/5.50  --abstr_ref_sig_restrict                funpre
% 39.33/5.50  --abstr_ref_af_restrict_to_split_sk     false
% 39.33/5.50  --abstr_ref_under                       []
% 39.33/5.50  
% 39.33/5.50  ------ SAT Options
% 39.33/5.50  
% 39.33/5.50  --sat_mode                              false
% 39.33/5.50  --sat_fm_restart_options                ""
% 39.33/5.50  --sat_gr_def                            false
% 39.33/5.50  --sat_epr_types                         true
% 39.33/5.50  --sat_non_cyclic_types                  false
% 39.33/5.50  --sat_finite_models                     false
% 39.33/5.50  --sat_fm_lemmas                         false
% 39.33/5.50  --sat_fm_prep                           false
% 39.33/5.50  --sat_fm_uc_incr                        true
% 39.33/5.50  --sat_out_model                         small
% 39.33/5.50  --sat_out_clauses                       false
% 39.33/5.50  
% 39.33/5.50  ------ QBF Options
% 39.33/5.50  
% 39.33/5.50  --qbf_mode                              false
% 39.33/5.50  --qbf_elim_univ                         false
% 39.33/5.50  --qbf_dom_inst                          none
% 39.33/5.50  --qbf_dom_pre_inst                      false
% 39.33/5.50  --qbf_sk_in                             false
% 39.33/5.50  --qbf_pred_elim                         true
% 39.33/5.50  --qbf_split                             512
% 39.33/5.50  
% 39.33/5.50  ------ BMC1 Options
% 39.33/5.50  
% 39.33/5.50  --bmc1_incremental                      false
% 39.33/5.50  --bmc1_axioms                           reachable_all
% 39.33/5.50  --bmc1_min_bound                        0
% 39.33/5.50  --bmc1_max_bound                        -1
% 39.33/5.50  --bmc1_max_bound_default                -1
% 39.33/5.50  --bmc1_symbol_reachability              true
% 39.33/5.50  --bmc1_property_lemmas                  false
% 39.33/5.50  --bmc1_k_induction                      false
% 39.33/5.50  --bmc1_non_equiv_states                 false
% 39.33/5.50  --bmc1_deadlock                         false
% 39.33/5.50  --bmc1_ucm                              false
% 39.33/5.50  --bmc1_add_unsat_core                   none
% 39.33/5.50  --bmc1_unsat_core_children              false
% 39.33/5.50  --bmc1_unsat_core_extrapolate_axioms    false
% 39.33/5.50  --bmc1_out_stat                         full
% 39.33/5.50  --bmc1_ground_init                      false
% 39.33/5.50  --bmc1_pre_inst_next_state              false
% 39.33/5.50  --bmc1_pre_inst_state                   false
% 39.33/5.50  --bmc1_pre_inst_reach_state             false
% 39.33/5.50  --bmc1_out_unsat_core                   false
% 39.33/5.50  --bmc1_aig_witness_out                  false
% 39.33/5.50  --bmc1_verbose                          false
% 39.33/5.50  --bmc1_dump_clauses_tptp                false
% 39.33/5.50  --bmc1_dump_unsat_core_tptp             false
% 39.33/5.50  --bmc1_dump_file                        -
% 39.33/5.50  --bmc1_ucm_expand_uc_limit              128
% 39.33/5.50  --bmc1_ucm_n_expand_iterations          6
% 39.33/5.50  --bmc1_ucm_extend_mode                  1
% 39.33/5.50  --bmc1_ucm_init_mode                    2
% 39.33/5.50  --bmc1_ucm_cone_mode                    none
% 39.33/5.50  --bmc1_ucm_reduced_relation_type        0
% 39.33/5.50  --bmc1_ucm_relax_model                  4
% 39.33/5.50  --bmc1_ucm_full_tr_after_sat            true
% 39.33/5.50  --bmc1_ucm_expand_neg_assumptions       false
% 39.33/5.50  --bmc1_ucm_layered_model                none
% 39.33/5.50  --bmc1_ucm_max_lemma_size               10
% 39.33/5.50  
% 39.33/5.50  ------ AIG Options
% 39.33/5.50  
% 39.33/5.50  --aig_mode                              false
% 39.33/5.50  
% 39.33/5.50  ------ Instantiation Options
% 39.33/5.50  
% 39.33/5.50  --instantiation_flag                    true
% 39.33/5.50  --inst_sos_flag                         true
% 39.33/5.50  --inst_sos_phase                        true
% 39.33/5.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.33/5.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.33/5.50  --inst_lit_sel_side                     none
% 39.33/5.50  --inst_solver_per_active                1400
% 39.33/5.50  --inst_solver_calls_frac                1.
% 39.33/5.50  --inst_passive_queue_type               priority_queues
% 39.33/5.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.33/5.50  --inst_passive_queues_freq              [25;2]
% 39.33/5.50  --inst_dismatching                      true
% 39.33/5.50  --inst_eager_unprocessed_to_passive     true
% 39.33/5.50  --inst_prop_sim_given                   true
% 39.33/5.50  --inst_prop_sim_new                     false
% 39.33/5.50  --inst_subs_new                         false
% 39.33/5.50  --inst_eq_res_simp                      false
% 39.33/5.50  --inst_subs_given                       false
% 39.33/5.50  --inst_orphan_elimination               true
% 39.33/5.50  --inst_learning_loop_flag               true
% 39.33/5.50  --inst_learning_start                   3000
% 39.33/5.50  --inst_learning_factor                  2
% 39.33/5.50  --inst_start_prop_sim_after_learn       3
% 39.33/5.50  --inst_sel_renew                        solver
% 39.33/5.50  --inst_lit_activity_flag                true
% 39.33/5.50  --inst_restr_to_given                   false
% 39.33/5.50  --inst_activity_threshold               500
% 39.33/5.50  --inst_out_proof                        true
% 39.33/5.50  
% 39.33/5.50  ------ Resolution Options
% 39.33/5.50  
% 39.33/5.50  --resolution_flag                       false
% 39.33/5.50  --res_lit_sel                           adaptive
% 39.33/5.50  --res_lit_sel_side                      none
% 39.33/5.50  --res_ordering                          kbo
% 39.33/5.50  --res_to_prop_solver                    active
% 39.33/5.50  --res_prop_simpl_new                    false
% 39.33/5.50  --res_prop_simpl_given                  true
% 39.33/5.50  --res_passive_queue_type                priority_queues
% 39.33/5.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.33/5.50  --res_passive_queues_freq               [15;5]
% 39.33/5.50  --res_forward_subs                      full
% 39.33/5.50  --res_backward_subs                     full
% 39.33/5.50  --res_forward_subs_resolution           true
% 39.33/5.50  --res_backward_subs_resolution          true
% 39.33/5.50  --res_orphan_elimination                true
% 39.33/5.50  --res_time_limit                        2.
% 39.33/5.50  --res_out_proof                         true
% 39.33/5.50  
% 39.33/5.50  ------ Superposition Options
% 39.33/5.50  
% 39.33/5.50  --superposition_flag                    true
% 39.33/5.50  --sup_passive_queue_type                priority_queues
% 39.33/5.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.33/5.50  --sup_passive_queues_freq               [8;1;4]
% 39.33/5.50  --demod_completeness_check              fast
% 39.33/5.50  --demod_use_ground                      true
% 39.33/5.50  --sup_to_prop_solver                    passive
% 39.33/5.50  --sup_prop_simpl_new                    true
% 39.33/5.50  --sup_prop_simpl_given                  true
% 39.33/5.50  --sup_fun_splitting                     true
% 39.33/5.50  --sup_smt_interval                      50000
% 39.33/5.50  
% 39.33/5.50  ------ Superposition Simplification Setup
% 39.33/5.50  
% 39.33/5.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.33/5.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.33/5.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.33/5.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.33/5.50  --sup_full_triv                         [TrivRules;PropSubs]
% 39.33/5.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.33/5.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.33/5.50  --sup_immed_triv                        [TrivRules]
% 39.33/5.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.33/5.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.33/5.50  --sup_immed_bw_main                     []
% 39.33/5.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.33/5.50  --sup_input_triv                        [Unflattening;TrivRules]
% 39.33/5.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.33/5.50  --sup_input_bw                          []
% 39.33/5.50  
% 39.33/5.50  ------ Combination Options
% 39.33/5.50  
% 39.33/5.50  --comb_res_mult                         3
% 39.33/5.50  --comb_sup_mult                         2
% 39.33/5.50  --comb_inst_mult                        10
% 39.33/5.50  
% 39.33/5.50  ------ Debug Options
% 39.33/5.50  
% 39.33/5.50  --dbg_backtrace                         false
% 39.33/5.50  --dbg_dump_prop_clauses                 false
% 39.33/5.50  --dbg_dump_prop_clauses_file            -
% 39.33/5.50  --dbg_out_stat                          false
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  ------ Proving...
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  % SZS status Theorem for theBenchmark.p
% 39.33/5.50  
% 39.33/5.50  % SZS output start CNFRefutation for theBenchmark.p
% 39.33/5.50  
% 39.33/5.50  fof(f13,conjecture,(
% 39.33/5.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f14,negated_conjecture,(
% 39.33/5.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 39.33/5.50    inference(negated_conjecture,[],[f13])).
% 39.33/5.50  
% 39.33/5.50  fof(f25,plain,(
% 39.33/5.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.33/5.50    inference(ennf_transformation,[],[f14])).
% 39.33/5.50  
% 39.33/5.50  fof(f34,plain,(
% 39.33/5.50    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,sK3)),k3_subset_1(X0,X1)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 39.33/5.50    introduced(choice_axiom,[])).
% 39.33/5.50  
% 39.33/5.50  fof(f33,plain,(
% 39.33/5.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 39.33/5.50    introduced(choice_axiom,[])).
% 39.33/5.50  
% 39.33/5.50  fof(f35,plain,(
% 39.33/5.50    (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 39.33/5.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f34,f33])).
% 39.33/5.50  
% 39.33/5.50  fof(f56,plain,(
% 39.33/5.50    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 39.33/5.50    inference(cnf_transformation,[],[f35])).
% 39.33/5.50  
% 39.33/5.50  fof(f9,axiom,(
% 39.33/5.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f21,plain,(
% 39.33/5.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 39.33/5.50    inference(ennf_transformation,[],[f9])).
% 39.33/5.50  
% 39.33/5.50  fof(f32,plain,(
% 39.33/5.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 39.33/5.50    inference(nnf_transformation,[],[f21])).
% 39.33/5.50  
% 39.33/5.50  fof(f49,plain,(
% 39.33/5.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f32])).
% 39.33/5.50  
% 39.33/5.50  fof(f11,axiom,(
% 39.33/5.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f54,plain,(
% 39.33/5.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f11])).
% 39.33/5.50  
% 39.33/5.50  fof(f8,axiom,(
% 39.33/5.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f28,plain,(
% 39.33/5.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 39.33/5.50    inference(nnf_transformation,[],[f8])).
% 39.33/5.50  
% 39.33/5.50  fof(f29,plain,(
% 39.33/5.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 39.33/5.50    inference(rectify,[],[f28])).
% 39.33/5.50  
% 39.33/5.50  fof(f30,plain,(
% 39.33/5.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 39.33/5.50    introduced(choice_axiom,[])).
% 39.33/5.50  
% 39.33/5.50  fof(f31,plain,(
% 39.33/5.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 39.33/5.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 39.33/5.50  
% 39.33/5.50  fof(f45,plain,(
% 39.33/5.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 39.33/5.50    inference(cnf_transformation,[],[f31])).
% 39.33/5.50  
% 39.33/5.50  fof(f62,plain,(
% 39.33/5.50    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 39.33/5.50    inference(equality_resolution,[],[f45])).
% 39.33/5.50  
% 39.33/5.50  fof(f2,axiom,(
% 39.33/5.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f15,plain,(
% 39.33/5.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 39.33/5.50    inference(ennf_transformation,[],[f2])).
% 39.33/5.50  
% 39.33/5.50  fof(f39,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f15])).
% 39.33/5.50  
% 39.33/5.50  fof(f57,plain,(
% 39.33/5.50    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 39.33/5.50    inference(cnf_transformation,[],[f35])).
% 39.33/5.50  
% 39.33/5.50  fof(f1,axiom,(
% 39.33/5.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f26,plain,(
% 39.33/5.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.33/5.50    inference(nnf_transformation,[],[f1])).
% 39.33/5.50  
% 39.33/5.50  fof(f27,plain,(
% 39.33/5.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.33/5.50    inference(flattening,[],[f26])).
% 39.33/5.50  
% 39.33/5.50  fof(f37,plain,(
% 39.33/5.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 39.33/5.50    inference(cnf_transformation,[],[f27])).
% 39.33/5.50  
% 39.33/5.50  fof(f59,plain,(
% 39.33/5.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.33/5.50    inference(equality_resolution,[],[f37])).
% 39.33/5.50  
% 39.33/5.50  fof(f5,axiom,(
% 39.33/5.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f19,plain,(
% 39.33/5.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 39.33/5.50    inference(ennf_transformation,[],[f5])).
% 39.33/5.50  
% 39.33/5.50  fof(f42,plain,(
% 39.33/5.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f19])).
% 39.33/5.50  
% 39.33/5.50  fof(f3,axiom,(
% 39.33/5.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f16,plain,(
% 39.33/5.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 39.33/5.50    inference(ennf_transformation,[],[f3])).
% 39.33/5.50  
% 39.33/5.50  fof(f17,plain,(
% 39.33/5.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 39.33/5.50    inference(flattening,[],[f16])).
% 39.33/5.50  
% 39.33/5.50  fof(f40,plain,(
% 39.33/5.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f17])).
% 39.33/5.50  
% 39.33/5.50  fof(f7,axiom,(
% 39.33/5.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f44,plain,(
% 39.33/5.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f7])).
% 39.33/5.50  
% 39.33/5.50  fof(f6,axiom,(
% 39.33/5.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f20,plain,(
% 39.33/5.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 39.33/5.50    inference(ennf_transformation,[],[f6])).
% 39.33/5.50  
% 39.33/5.50  fof(f43,plain,(
% 39.33/5.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f20])).
% 39.33/5.50  
% 39.33/5.50  fof(f46,plain,(
% 39.33/5.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 39.33/5.50    inference(cnf_transformation,[],[f31])).
% 39.33/5.50  
% 39.33/5.50  fof(f61,plain,(
% 39.33/5.50    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 39.33/5.50    inference(equality_resolution,[],[f46])).
% 39.33/5.50  
% 39.33/5.50  fof(f50,plain,(
% 39.33/5.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f32])).
% 39.33/5.50  
% 39.33/5.50  fof(f10,axiom,(
% 39.33/5.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f22,plain,(
% 39.33/5.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.33/5.50    inference(ennf_transformation,[],[f10])).
% 39.33/5.50  
% 39.33/5.50  fof(f53,plain,(
% 39.33/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f22])).
% 39.33/5.50  
% 39.33/5.50  fof(f4,axiom,(
% 39.33/5.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f18,plain,(
% 39.33/5.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 39.33/5.50    inference(ennf_transformation,[],[f4])).
% 39.33/5.50  
% 39.33/5.50  fof(f41,plain,(
% 39.33/5.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f18])).
% 39.33/5.50  
% 39.33/5.50  fof(f12,axiom,(
% 39.33/5.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 39.33/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.33/5.50  
% 39.33/5.50  fof(f23,plain,(
% 39.33/5.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 39.33/5.50    inference(ennf_transformation,[],[f12])).
% 39.33/5.50  
% 39.33/5.50  fof(f24,plain,(
% 39.33/5.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.33/5.50    inference(flattening,[],[f23])).
% 39.33/5.50  
% 39.33/5.50  fof(f55,plain,(
% 39.33/5.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.33/5.50    inference(cnf_transformation,[],[f24])).
% 39.33/5.50  
% 39.33/5.50  fof(f38,plain,(
% 39.33/5.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 39.33/5.50    inference(cnf_transformation,[],[f27])).
% 39.33/5.50  
% 39.33/5.50  fof(f36,plain,(
% 39.33/5.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 39.33/5.50    inference(cnf_transformation,[],[f27])).
% 39.33/5.50  
% 39.33/5.50  fof(f60,plain,(
% 39.33/5.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.33/5.50    inference(equality_resolution,[],[f36])).
% 39.33/5.50  
% 39.33/5.50  fof(f58,plain,(
% 39.33/5.50    ~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 39.33/5.50    inference(cnf_transformation,[],[f35])).
% 39.33/5.50  
% 39.33/5.50  cnf(c_22,negated_conjecture,
% 39.33/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 39.33/5.50      inference(cnf_transformation,[],[f56]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1222,plain,
% 39.33/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_16,plain,
% 39.33/5.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 39.33/5.50      inference(cnf_transformation,[],[f49]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1228,plain,
% 39.33/5.50      ( m1_subset_1(X0,X1) != iProver_top
% 39.33/5.50      | r2_hidden(X0,X1) = iProver_top
% 39.33/5.50      | v1_xboole_0(X1) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1872,plain,
% 39.33/5.50      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 39.33/5.50      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_1222,c_1228]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_18,plain,
% 39.33/5.50      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 39.33/5.50      inference(cnf_transformation,[],[f54]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_29,plain,
% 39.33/5.50      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_31,plain,
% 39.33/5.50      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_29]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2128,plain,
% 39.33/5.50      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 39.33/5.50      inference(global_propositional_subsumption,
% 39.33/5.50                [status(thm)],
% 39.33/5.50                [c_1872,c_31]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_12,plain,
% 39.33/5.50      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 39.33/5.50      inference(cnf_transformation,[],[f62]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1232,plain,
% 39.33/5.50      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 39.33/5.50      | r1_tarski(X0,X1) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2132,plain,
% 39.33/5.50      ( r1_tarski(sK2,sK1) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_2128,c_1232]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_3,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 39.33/5.50      inference(cnf_transformation,[],[f39]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1241,plain,
% 39.33/5.50      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2212,plain,
% 39.33/5.50      ( k2_xboole_0(sK2,sK1) = sK1 ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_2132,c_1241]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_21,negated_conjecture,
% 39.33/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 39.33/5.50      inference(cnf_transformation,[],[f57]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1223,plain,
% 39.33/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1871,plain,
% 39.33/5.50      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 39.33/5.50      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_1223,c_1228]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2121,plain,
% 39.33/5.50      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 39.33/5.50      inference(global_propositional_subsumption,
% 39.33/5.50                [status(thm)],
% 39.33/5.50                [c_1871,c_31]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2125,plain,
% 39.33/5.50      ( r1_tarski(sK3,sK1) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_2121,c_1232]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1,plain,
% 39.33/5.50      ( r1_tarski(X0,X0) ),
% 39.33/5.50      inference(cnf_transformation,[],[f59]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1242,plain,
% 39.33/5.50      ( r1_tarski(X0,X0) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 39.33/5.50      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 39.33/5.50      inference(cnf_transformation,[],[f42]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1238,plain,
% 39.33/5.50      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 39.33/5.50      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2354,plain,
% 39.33/5.50      ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_1242,c_1238]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_4,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 39.33/5.50      inference(cnf_transformation,[],[f40]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1240,plain,
% 39.33/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.33/5.50      | r1_tarski(X1,X2) != iProver_top
% 39.33/5.50      | r1_tarski(X0,X2) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6041,plain,
% 39.33/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.33/5.50      | r1_tarski(k4_xboole_0(k2_xboole_0(X2,X0),X2),X1) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_2354,c_1240]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_104864,plain,
% 39.33/5.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X2) = X2
% 39.33/5.50      | r1_tarski(X1,X2) != iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_6041,c_1241]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_123730,plain,
% 39.33/5.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK3),X0),sK1) = sK1 ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_2125,c_104864]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_8,plain,
% 39.33/5.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 39.33/5.50      inference(cnf_transformation,[],[f44]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1236,plain,
% 39.33/5.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_7,plain,
% 39.33/5.50      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 39.33/5.50      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 39.33/5.50      inference(cnf_transformation,[],[f43]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1237,plain,
% 39.33/5.50      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 39.33/5.50      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2018,plain,
% 39.33/5.50      ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_1236,c_1237]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_125862,plain,
% 39.33/5.50      ( r1_tarski(k2_xboole_0(X0,sK3),k2_xboole_0(X0,sK1)) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_123730,c_2018]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_131396,plain,
% 39.33/5.50      ( k2_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(X0,sK1)) = k2_xboole_0(X0,sK1) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_125862,c_1241]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_132342,plain,
% 39.33/5.50      ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK1) = k2_xboole_0(sK2,sK1) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_2212,c_131396]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_132650,plain,
% 39.33/5.50      ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK1) = sK1 ),
% 39.33/5.50      inference(light_normalisation,[status(thm)],[c_132342,c_2212]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_11,plain,
% 39.33/5.50      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.33/5.50      inference(cnf_transformation,[],[f61]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1233,plain,
% 39.33/5.50      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 39.33/5.50      | r1_tarski(X0,X1) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_15,plain,
% 39.33/5.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 39.33/5.50      inference(cnf_transformation,[],[f50]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1229,plain,
% 39.33/5.50      ( m1_subset_1(X0,X1) = iProver_top
% 39.33/5.50      | r2_hidden(X0,X1) != iProver_top
% 39.33/5.50      | v1_xboole_0(X1) = iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2276,plain,
% 39.33/5.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 39.33/5.50      | r1_tarski(X0,X1) != iProver_top
% 39.33/5.50      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_1233,c_1229]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_182,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 39.33/5.50      inference(prop_impl,[status(thm)],[c_11]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_183,plain,
% 39.33/5.50      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.33/5.50      inference(renaming,[status(thm)],[c_182]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_370,plain,
% 39.33/5.50      ( m1_subset_1(X0,X1)
% 39.33/5.50      | ~ r1_tarski(X2,X3)
% 39.33/5.50      | v1_xboole_0(X1)
% 39.33/5.50      | X0 != X2
% 39.33/5.50      | k1_zfmisc_1(X3) != X1 ),
% 39.33/5.50      inference(resolution_lifted,[status(thm)],[c_183,c_15]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_371,plain,
% 39.33/5.50      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.33/5.50      | ~ r1_tarski(X0,X1)
% 39.33/5.50      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 39.33/5.50      inference(unflattening,[status(thm)],[c_370]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_381,plain,
% 39.33/5.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.33/5.50      inference(forward_subsumption_resolution,
% 39.33/5.50                [status(thm)],
% 39.33/5.50                [c_371,c_18]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_384,plain,
% 39.33/5.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 39.33/5.50      | r1_tarski(X0,X1) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_7250,plain,
% 39.33/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.33/5.50      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 39.33/5.50      inference(global_propositional_subsumption,
% 39.33/5.50                [status(thm)],
% 39.33/5.50                [c_2276,c_384]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_7251,plain,
% 39.33/5.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 39.33/5.50      | r1_tarski(X0,X1) != iProver_top ),
% 39.33/5.50      inference(renaming,[status(thm)],[c_7250]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_17,plain,
% 39.33/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.33/5.50      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 39.33/5.50      inference(cnf_transformation,[],[f53]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1227,plain,
% 39.33/5.50      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 39.33/5.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_7257,plain,
% 39.33/5.50      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 39.33/5.50      | r1_tarski(X1,X0) != iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_7251,c_1227]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_64248,plain,
% 39.33/5.50      ( k3_subset_1(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_1236,c_7257]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_133392,plain,
% 39.33/5.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK3),sK1),k2_xboole_0(sK2,sK3)) = k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_132650,c_64248]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_133462,plain,
% 39.33/5.50      ( k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
% 39.33/5.50      inference(demodulation,[status(thm)],[c_133392,c_132650]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_50617,plain,
% 39.33/5.50      ( r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_8]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_5,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,X1)
% 39.33/5.50      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 39.33/5.50      inference(cnf_transformation,[],[f41]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1839,plain,
% 39.33/5.50      ( r1_tarski(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK2))
% 39.33/5.50      | ~ r1_tarski(sK2,X0) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_5]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_22560,plain,
% 39.33/5.50      ( r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
% 39.33/5.50      | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_1839]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_726,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.33/5.50      theory(equality) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1302,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,X1)
% 39.33/5.50      | r1_tarski(X2,k3_subset_1(sK1,sK2))
% 39.33/5.50      | X2 != X0
% 39.33/5.50      | k3_subset_1(sK1,sK2) != X1 ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_726]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1426,plain,
% 39.33/5.50      ( r1_tarski(X0,k3_subset_1(sK1,sK2))
% 39.33/5.50      | ~ r1_tarski(X1,k4_xboole_0(sK1,sK2))
% 39.33/5.50      | X0 != X1
% 39.33/5.50      | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_1302]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1721,plain,
% 39.33/5.50      ( r1_tarski(X0,k3_subset_1(sK1,sK2))
% 39.33/5.50      | ~ r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(sK1,sK2))
% 39.33/5.50      | X0 != k4_xboole_0(X1,X2)
% 39.33/5.50      | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_1426]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_3541,plain,
% 39.33/5.50      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(sK1,sK2))
% 39.33/5.50      | ~ r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(sK1,sK2))
% 39.33/5.50      | k3_subset_1(X0,X1) != k4_xboole_0(X0,X1)
% 39.33/5.50      | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_1721]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_9401,plain,
% 39.33/5.50      ( r1_tarski(k3_subset_1(X0,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
% 39.33/5.50      | ~ r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
% 39.33/5.50      | k3_subset_1(X0,k2_xboole_0(sK2,sK3)) != k4_xboole_0(X0,k2_xboole_0(sK2,sK3))
% 39.33/5.50      | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_3541]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_9408,plain,
% 39.33/5.50      ( r1_tarski(k3_subset_1(sK1,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
% 39.33/5.50      | ~ r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
% 39.33/5.50      | k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) != k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
% 39.33/5.50      | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_9401]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1277,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,X1)
% 39.33/5.50      | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 39.33/5.50      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != X0
% 39.33/5.50      | k3_subset_1(sK1,sK2) != X1 ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_726]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1322,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,k3_subset_1(sK1,sK2))
% 39.33/5.50      | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 39.33/5.50      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != X0
% 39.33/5.50      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_1277]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1916,plain,
% 39.33/5.50      ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(sK1,sK2))
% 39.33/5.50      | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 39.33/5.50      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(X0,X1)
% 39.33/5.50      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_1322]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6235,plain,
% 39.33/5.50      ( ~ r1_tarski(k3_subset_1(X0,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
% 39.33/5.50      | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 39.33/5.50      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(X0,k2_xboole_0(sK2,sK3))
% 39.33/5.50      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_1916]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_6247,plain,
% 39.33/5.50      ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 39.33/5.50      | ~ r1_tarski(k3_subset_1(sK1,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
% 39.33/5.50      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(sK1,k2_xboole_0(sK2,sK3))
% 39.33/5.50      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_6235]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_19,plain,
% 39.33/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.33/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.33/5.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 39.33/5.50      inference(cnf_transformation,[],[f55]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1225,plain,
% 39.33/5.50      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 39.33/5.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 39.33/5.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 39.33/5.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_3475,plain,
% 39.33/5.50      ( k4_subset_1(sK1,sK2,X0) = k2_xboole_0(sK2,X0)
% 39.33/5.50      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_1222,c_1225]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_3674,plain,
% 39.33/5.50      ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) ),
% 39.33/5.50      inference(superposition,[status(thm)],[c_1223,c_3475]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_731,plain,
% 39.33/5.50      ( X0 != X1 | X2 != X3 | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
% 39.33/5.50      theory(equality) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1969,plain,
% 39.33/5.50      ( k4_subset_1(sK1,sK2,sK3) != X0
% 39.33/5.50      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(X1,X0)
% 39.33/5.50      | sK1 != X1 ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_731]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_3466,plain,
% 39.33/5.50      ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
% 39.33/5.50      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(X0,k2_xboole_0(sK2,sK3))
% 39.33/5.50      | sK1 != X0 ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_1969]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_3467,plain,
% 39.33/5.50      ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
% 39.33/5.50      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(sK1,k2_xboole_0(sK2,sK3))
% 39.33/5.50      | sK1 != sK1 ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_3466]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_724,plain,( X0 = X0 ),theory(equality) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1388,plain,
% 39.33/5.50      ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_724]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_1381,plain,
% 39.33/5.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 39.33/5.50      | k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_17]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_0,plain,
% 39.33/5.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 39.33/5.50      inference(cnf_transformation,[],[f38]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_76,plain,
% 39.33/5.50      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_0]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_2,plain,
% 39.33/5.50      ( r1_tarski(X0,X0) ),
% 39.33/5.50      inference(cnf_transformation,[],[f60]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_72,plain,
% 39.33/5.50      ( r1_tarski(sK1,sK1) ),
% 39.33/5.50      inference(instantiation,[status(thm)],[c_2]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(c_20,negated_conjecture,
% 39.33/5.50      ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
% 39.33/5.50      inference(cnf_transformation,[],[f58]) ).
% 39.33/5.50  
% 39.33/5.50  cnf(contradiction,plain,
% 39.33/5.50      ( $false ),
% 39.33/5.50      inference(minisat,
% 39.33/5.50                [status(thm)],
% 39.33/5.50                [c_133462,c_50617,c_22560,c_9408,c_6247,c_3674,c_3467,
% 39.33/5.50                 c_1388,c_1381,c_76,c_72,c_20,c_22]) ).
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 39.33/5.50  
% 39.33/5.50  ------                               Statistics
% 39.33/5.50  
% 39.33/5.50  ------ General
% 39.33/5.50  
% 39.33/5.50  abstr_ref_over_cycles:                  0
% 39.33/5.50  abstr_ref_under_cycles:                 0
% 39.33/5.50  gc_basic_clause_elim:                   0
% 39.33/5.50  forced_gc_time:                         0
% 39.33/5.50  parsing_time:                           0.025
% 39.33/5.50  unif_index_cands_time:                  0.
% 39.33/5.50  unif_index_add_time:                    0.
% 39.33/5.50  orderings_time:                         0.
% 39.33/5.50  out_proof_time:                         0.016
% 39.33/5.50  total_time:                             4.556
% 39.33/5.50  num_of_symbols:                         45
% 39.33/5.50  num_of_terms:                           156964
% 39.33/5.50  
% 39.33/5.50  ------ Preprocessing
% 39.33/5.50  
% 39.33/5.50  num_of_splits:                          0
% 39.33/5.50  num_of_split_atoms:                     1
% 39.33/5.50  num_of_reused_defs:                     0
% 39.33/5.50  num_eq_ax_congr_red:                    18
% 39.33/5.50  num_of_sem_filtered_clauses:            1
% 39.33/5.50  num_of_subtypes:                        0
% 39.33/5.50  monotx_restored_types:                  0
% 39.33/5.50  sat_num_of_epr_types:                   0
% 39.33/5.50  sat_num_of_non_cyclic_types:            0
% 39.33/5.50  sat_guarded_non_collapsed_types:        0
% 39.33/5.50  num_pure_diseq_elim:                    0
% 39.33/5.50  simp_replaced_by:                       0
% 39.33/5.50  res_preprocessed:                       107
% 39.33/5.50  prep_upred:                             0
% 39.33/5.50  prep_unflattend:                        24
% 39.33/5.50  smt_new_axioms:                         0
% 39.33/5.50  pred_elim_cands:                        4
% 39.33/5.50  pred_elim:                              0
% 39.33/5.50  pred_elim_cl:                           0
% 39.33/5.50  pred_elim_cycles:                       2
% 39.33/5.50  merged_defs:                            16
% 39.33/5.50  merged_defs_ncl:                        0
% 39.33/5.50  bin_hyper_res:                          16
% 39.33/5.50  prep_cycles:                            4
% 39.33/5.50  pred_elim_time:                         0.004
% 39.33/5.50  splitting_time:                         0.
% 39.33/5.50  sem_filter_time:                        0.
% 39.33/5.50  monotx_time:                            0.001
% 39.33/5.50  subtype_inf_time:                       0.
% 39.33/5.50  
% 39.33/5.50  ------ Problem properties
% 39.33/5.50  
% 39.33/5.50  clauses:                                22
% 39.33/5.50  conjectures:                            3
% 39.33/5.50  epr:                                    7
% 39.33/5.50  horn:                                   19
% 39.33/5.50  ground:                                 3
% 39.33/5.50  unary:                                  6
% 39.33/5.50  binary:                                 7
% 39.33/5.50  lits:                                   47
% 39.33/5.50  lits_eq:                                6
% 39.33/5.50  fd_pure:                                0
% 39.33/5.50  fd_pseudo:                              0
% 39.33/5.50  fd_cond:                                0
% 39.33/5.50  fd_pseudo_cond:                         3
% 39.33/5.50  ac_symbols:                             0
% 39.33/5.50  
% 39.33/5.50  ------ Propositional Solver
% 39.33/5.50  
% 39.33/5.50  prop_solver_calls:                      59
% 39.33/5.50  prop_fast_solver_calls:                 1546
% 39.33/5.50  smt_solver_calls:                       0
% 39.33/5.50  smt_fast_solver_calls:                  0
% 39.33/5.50  prop_num_of_clauses:                    58463
% 39.33/5.50  prop_preprocess_simplified:             72814
% 39.33/5.50  prop_fo_subsumed:                       5
% 39.33/5.50  prop_solver_time:                       0.
% 39.33/5.50  smt_solver_time:                        0.
% 39.33/5.50  smt_fast_solver_time:                   0.
% 39.33/5.50  prop_fast_solver_time:                  0.
% 39.33/5.50  prop_unsat_core_time:                   0.005
% 39.33/5.50  
% 39.33/5.50  ------ QBF
% 39.33/5.50  
% 39.33/5.50  qbf_q_res:                              0
% 39.33/5.50  qbf_num_tautologies:                    0
% 39.33/5.50  qbf_prep_cycles:                        0
% 39.33/5.50  
% 39.33/5.50  ------ BMC1
% 39.33/5.50  
% 39.33/5.50  bmc1_current_bound:                     -1
% 39.33/5.50  bmc1_last_solved_bound:                 -1
% 39.33/5.50  bmc1_unsat_core_size:                   -1
% 39.33/5.50  bmc1_unsat_core_parents_size:           -1
% 39.33/5.50  bmc1_merge_next_fun:                    0
% 39.33/5.50  bmc1_unsat_core_clauses_time:           0.
% 39.33/5.50  
% 39.33/5.50  ------ Instantiation
% 39.33/5.50  
% 39.33/5.50  inst_num_of_clauses:                    1436
% 39.33/5.50  inst_num_in_passive:                    273
% 39.33/5.50  inst_num_in_active:                     2886
% 39.33/5.50  inst_num_in_unprocessed:                549
% 39.33/5.50  inst_num_of_loops:                      3659
% 39.33/5.50  inst_num_of_learning_restarts:          1
% 39.33/5.50  inst_num_moves_active_passive:          770
% 39.33/5.50  inst_lit_activity:                      0
% 39.33/5.50  inst_lit_activity_moves:                0
% 39.33/5.50  inst_num_tautologies:                   0
% 39.33/5.50  inst_num_prop_implied:                  0
% 39.33/5.50  inst_num_existing_simplified:           0
% 39.33/5.50  inst_num_eq_res_simplified:             0
% 39.33/5.50  inst_num_child_elim:                    0
% 39.33/5.50  inst_num_of_dismatching_blockings:      12022
% 39.33/5.50  inst_num_of_non_proper_insts:           16387
% 39.33/5.50  inst_num_of_duplicates:                 0
% 39.33/5.50  inst_inst_num_from_inst_to_res:         0
% 39.33/5.50  inst_dismatching_checking_time:         0.
% 39.33/5.50  
% 39.33/5.50  ------ Resolution
% 39.33/5.50  
% 39.33/5.50  res_num_of_clauses:                     31
% 39.33/5.50  res_num_in_passive:                     31
% 39.33/5.50  res_num_in_active:                      0
% 39.33/5.50  res_num_of_loops:                       111
% 39.33/5.50  res_forward_subset_subsumed:            2508
% 39.33/5.50  res_backward_subset_subsumed:           0
% 39.33/5.50  res_forward_subsumed:                   0
% 39.33/5.50  res_backward_subsumed:                  0
% 39.33/5.50  res_forward_subsumption_resolution:     2
% 39.33/5.50  res_backward_subsumption_resolution:    0
% 39.33/5.50  res_clause_to_clause_subsumption:       152073
% 39.33/5.50  res_orphan_elimination:                 0
% 39.33/5.50  res_tautology_del:                      1990
% 39.33/5.50  res_num_eq_res_simplified:              0
% 39.33/5.50  res_num_sel_changes:                    0
% 39.33/5.50  res_moves_from_active_to_pass:          0
% 39.33/5.50  
% 39.33/5.50  ------ Superposition
% 39.33/5.50  
% 39.33/5.50  sup_time_total:                         0.
% 39.33/5.50  sup_time_generating:                    0.
% 39.33/5.50  sup_time_sim_full:                      0.
% 39.33/5.50  sup_time_sim_immed:                     0.
% 39.33/5.50  
% 39.33/5.50  sup_num_of_clauses:                     14127
% 39.33/5.50  sup_num_in_active:                      725
% 39.33/5.50  sup_num_in_passive:                     13402
% 39.33/5.50  sup_num_of_loops:                       731
% 39.33/5.50  sup_fw_superposition:                   10459
% 39.33/5.50  sup_bw_superposition:                   10808
% 39.33/5.50  sup_immediate_simplified:               7007
% 39.33/5.50  sup_given_eliminated:                   1
% 39.33/5.50  comparisons_done:                       0
% 39.33/5.50  comparisons_avoided:                    18
% 39.33/5.50  
% 39.33/5.50  ------ Simplifications
% 39.33/5.50  
% 39.33/5.50  
% 39.33/5.50  sim_fw_subset_subsumed:                 520
% 39.33/5.50  sim_bw_subset_subsumed:                 165
% 39.33/5.50  sim_fw_subsumed:                        779
% 39.33/5.50  sim_bw_subsumed:                        23
% 39.33/5.50  sim_fw_subsumption_res:                 0
% 39.33/5.50  sim_bw_subsumption_res:                 0
% 39.33/5.50  sim_tautology_del:                      70
% 39.33/5.50  sim_eq_tautology_del:                   1739
% 39.33/5.50  sim_eq_res_simp:                        0
% 39.33/5.50  sim_fw_demodulated:                     4208
% 39.33/5.50  sim_bw_demodulated:                     67
% 39.33/5.50  sim_light_normalised:                   2917
% 39.33/5.50  sim_joinable_taut:                      0
% 39.33/5.50  sim_joinable_simp:                      0
% 39.33/5.50  sim_ac_normalised:                      0
% 39.33/5.50  sim_smt_subsumption:                    0
% 39.33/5.50  
%------------------------------------------------------------------------------
