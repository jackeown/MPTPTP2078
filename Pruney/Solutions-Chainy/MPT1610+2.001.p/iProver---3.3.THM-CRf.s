%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:16 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 194 expanded)
%              Number of clauses        :   40 (  59 expanded)
%              Number of leaves         :   16 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  256 ( 499 expanded)
%              Number of equality atoms :  106 ( 214 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k9_setfam_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(k9_setfam_1(X0),k9_setfam_1(X1)) = k9_setfam_1(k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f51,f52,f52,f52])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f13,conjecture,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,
    ( ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))
   => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK2)) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f31])).

fof(f55,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK2))) ),
    inference(definition_unfolding,[],[f55,f54])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k9_setfam_1(X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8391,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k9_setfam_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_19,plain,
    ( ~ r2_hidden(k1_xboole_0,X0)
    | v1_xboole_0(X0)
    | k3_yellow_0(k2_yellow_1(X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_229,plain,
    ( ~ r2_hidden(k1_xboole_0,X0)
    | k3_yellow_0(k2_yellow_1(X0)) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_19,c_7])).

cnf(c_8386,plain,
    ( k3_yellow_0(k2_yellow_1(X0)) = k1_xboole_0
    | k1_xboole_0 = X0
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_8577,plain,
    ( k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = k1_xboole_0
    | k9_setfam_1(X0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8391,c_8386])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_42,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_44,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_3408,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3407,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k9_setfam_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3405,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3508,plain,
    ( k2_xboole_0(k1_tarski(X0),k9_setfam_1(X1)) = k9_setfam_1(X1)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3407,c_3405])).

cnf(c_3535,plain,
    ( k2_xboole_0(k1_tarski(X0),k9_setfam_1(X0)) = k9_setfam_1(X0) ),
    inference(superposition,[status(thm)],[c_3408,c_3508])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3538,plain,
    ( k9_setfam_1(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3535,c_17])).

cnf(c_11,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8472,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_18,plain,
    ( k3_xboole_0(k9_setfam_1(X0),k9_setfam_1(X1)) = k9_setfam_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8496,plain,
    ( k3_xboole_0(k9_setfam_1(X0),k9_setfam_1(X1)) = k9_setfam_1(k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_18])).

cnf(c_8508,plain,
    ( k9_setfam_1(k3_xboole_0(X0,X1)) = k9_setfam_1(k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8496,c_18])).

cnf(c_8529,plain,
    ( k3_xboole_0(k9_setfam_1(k3_xboole_0(X0,X1)),k9_setfam_1(X2)) = k9_setfam_1(k3_xboole_0(k3_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_8508,c_18])).

cnf(c_9142,plain,
    ( k9_setfam_1(k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = k3_xboole_0(k9_setfam_1(k1_xboole_0),k9_setfam_1(X1)) ),
    inference(superposition,[status(thm)],[c_8472,c_8529])).

cnf(c_9217,plain,
    ( k3_xboole_0(k9_setfam_1(k1_xboole_0),k9_setfam_1(X0)) = k9_setfam_1(k3_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_9142,c_11])).

cnf(c_9218,plain,
    ( k3_xboole_0(k9_setfam_1(k1_xboole_0),k9_setfam_1(X0)) = k9_setfam_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_9217,c_8472,c_8496])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8395,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9853,plain,
    ( r2_hidden(X0,k9_setfam_1(X1)) = iProver_top
    | r2_hidden(X0,k9_setfam_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9218,c_8395])).

cnf(c_10294,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X0,k9_setfam_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8391,c_9853])).

cnf(c_10317,plain,
    ( k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = k1_xboole_0
    | k9_setfam_1(X0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10294,c_8386])).

cnf(c_14883,plain,
    ( k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8577,c_44,c_3538,c_10317])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_14886,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14883,c_20])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_47,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_43,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14886,c_47,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.01/1.14  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.14  
% 3.01/1.14  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/1.14  
% 3.01/1.14  ------  iProver source info
% 3.01/1.14  
% 3.01/1.14  git: date: 2020-06-30 10:37:57 +0100
% 3.01/1.14  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/1.14  git: non_committed_changes: false
% 3.01/1.14  git: last_make_outside_of_git: false
% 3.01/1.14  
% 3.01/1.14  ------ 
% 3.01/1.14  ------ Parsing...
% 3.01/1.14  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  ------ Proving...
% 3.01/1.14  ------ Problem Properties 
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  clauses                                 19
% 3.01/1.14  conjectures                             2
% 3.01/1.14  EPR                                     2
% 3.01/1.14  Horn                                    15
% 3.01/1.14  unary                                   6
% 3.01/1.14  binary                                  5
% 3.01/1.14  lits                                    41
% 3.01/1.14  lits eq                                 14
% 3.01/1.14  fd_pure                                 0
% 3.01/1.14  fd_pseudo                               0
% 3.01/1.14  fd_cond                                 1
% 3.01/1.14  fd_pseudo_cond                          6
% 3.01/1.14  AC symbols                              0
% 3.01/1.14  
% 3.01/1.14  ------ Input Options Time Limit: Unbounded
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.01/1.14  Current options:
% 3.01/1.14  ------ 
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing...
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing...
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.01/1.14  
% 3.01/1.14  ------ Proving...
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  % SZS status Theorem for theBenchmark.p
% 3.01/1.14  
% 3.01/1.14  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/1.14  
% 3.01/1.14  fof(f6,axiom,(
% 3.01/1.14    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f27,plain,(
% 3.01/1.14    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.01/1.14    inference(nnf_transformation,[],[f6])).
% 3.01/1.14  
% 3.01/1.14  fof(f28,plain,(
% 3.01/1.14    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.01/1.14    inference(rectify,[],[f27])).
% 3.01/1.14  
% 3.01/1.14  fof(f29,plain,(
% 3.01/1.14    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.01/1.14    introduced(choice_axiom,[])).
% 3.01/1.14  
% 3.01/1.14  fof(f30,plain,(
% 3.01/1.14    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.01/1.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 3.01/1.14  
% 3.01/1.14  fof(f46,plain,(
% 3.01/1.14    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.01/1.14    inference(cnf_transformation,[],[f30])).
% 3.01/1.14  
% 3.01/1.14  fof(f10,axiom,(
% 3.01/1.14    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f52,plain,(
% 3.01/1.14    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 3.01/1.14    inference(cnf_transformation,[],[f10])).
% 3.01/1.14  
% 3.01/1.14  fof(f58,plain,(
% 3.01/1.14    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k9_setfam_1(X0) != X1) )),
% 3.01/1.14    inference(definition_unfolding,[],[f46,f52])).
% 3.01/1.14  
% 3.01/1.14  fof(f67,plain,(
% 3.01/1.14    ( ! [X0,X3] : (r2_hidden(X3,k9_setfam_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.01/1.14    inference(equality_resolution,[],[f58])).
% 3.01/1.14  
% 3.01/1.14  fof(f11,axiom,(
% 3.01/1.14    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f17,plain,(
% 3.01/1.14    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 3.01/1.14    inference(ennf_transformation,[],[f11])).
% 3.01/1.14  
% 3.01/1.14  fof(f18,plain,(
% 3.01/1.14    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 3.01/1.14    inference(flattening,[],[f17])).
% 3.01/1.14  
% 3.01/1.14  fof(f53,plain,(
% 3.01/1.14    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 3.01/1.14    inference(cnf_transformation,[],[f18])).
% 3.01/1.14  
% 3.01/1.14  fof(f3,axiom,(
% 3.01/1.14    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f15,plain,(
% 3.01/1.14    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.01/1.14    inference(ennf_transformation,[],[f3])).
% 3.01/1.14  
% 3.01/1.14  fof(f40,plain,(
% 3.01/1.14    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.01/1.14    inference(cnf_transformation,[],[f15])).
% 3.01/1.14  
% 3.01/1.14  fof(f4,axiom,(
% 3.01/1.14    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f25,plain,(
% 3.01/1.14    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.01/1.14    inference(nnf_transformation,[],[f4])).
% 3.01/1.14  
% 3.01/1.14  fof(f26,plain,(
% 3.01/1.14    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.01/1.14    inference(flattening,[],[f25])).
% 3.01/1.14  
% 3.01/1.14  fof(f41,plain,(
% 3.01/1.14    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.01/1.14    inference(cnf_transformation,[],[f26])).
% 3.01/1.14  
% 3.01/1.14  fof(f66,plain,(
% 3.01/1.14    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.01/1.14    inference(equality_resolution,[],[f41])).
% 3.01/1.14  
% 3.01/1.14  fof(f7,axiom,(
% 3.01/1.14    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f16,plain,(
% 3.01/1.14    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 3.01/1.14    inference(ennf_transformation,[],[f7])).
% 3.01/1.14  
% 3.01/1.14  fof(f49,plain,(
% 3.01/1.14    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.01/1.14    inference(cnf_transformation,[],[f16])).
% 3.01/1.14  
% 3.01/1.14  fof(f8,axiom,(
% 3.01/1.14    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f50,plain,(
% 3.01/1.14    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 3.01/1.14    inference(cnf_transformation,[],[f8])).
% 3.01/1.14  
% 3.01/1.14  fof(f5,axiom,(
% 3.01/1.14    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f44,plain,(
% 3.01/1.14    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.01/1.14    inference(cnf_transformation,[],[f5])).
% 3.01/1.14  
% 3.01/1.14  fof(f1,axiom,(
% 3.01/1.14    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f33,plain,(
% 3.01/1.14    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.01/1.14    inference(cnf_transformation,[],[f1])).
% 3.01/1.14  
% 3.01/1.14  fof(f9,axiom,(
% 3.01/1.14    ! [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1))),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f51,plain,(
% 3.01/1.14    ( ! [X0,X1] : (k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1))) )),
% 3.01/1.14    inference(cnf_transformation,[],[f9])).
% 3.01/1.14  
% 3.01/1.14  fof(f60,plain,(
% 3.01/1.14    ( ! [X0,X1] : (k3_xboole_0(k9_setfam_1(X0),k9_setfam_1(X1)) = k9_setfam_1(k3_xboole_0(X0,X1))) )),
% 3.01/1.14    inference(definition_unfolding,[],[f51,f52,f52,f52])).
% 3.01/1.14  
% 3.01/1.14  fof(f2,axiom,(
% 3.01/1.14    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f20,plain,(
% 3.01/1.14    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.01/1.14    inference(nnf_transformation,[],[f2])).
% 3.01/1.14  
% 3.01/1.14  fof(f21,plain,(
% 3.01/1.14    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.01/1.14    inference(flattening,[],[f20])).
% 3.01/1.14  
% 3.01/1.14  fof(f22,plain,(
% 3.01/1.14    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.01/1.14    inference(rectify,[],[f21])).
% 3.01/1.14  
% 3.01/1.14  fof(f23,plain,(
% 3.01/1.14    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.01/1.14    introduced(choice_axiom,[])).
% 3.01/1.14  
% 3.01/1.14  fof(f24,plain,(
% 3.01/1.14    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.01/1.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.01/1.14  
% 3.01/1.14  fof(f35,plain,(
% 3.01/1.14    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.01/1.14    inference(cnf_transformation,[],[f24])).
% 3.01/1.14  
% 3.01/1.14  fof(f63,plain,(
% 3.01/1.14    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.01/1.14    inference(equality_resolution,[],[f35])).
% 3.01/1.14  
% 3.01/1.14  fof(f13,conjecture,(
% 3.01/1.14    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f14,negated_conjecture,(
% 3.01/1.14    ~! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 3.01/1.14    inference(negated_conjecture,[],[f13])).
% 3.01/1.14  
% 3.01/1.14  fof(f19,plain,(
% 3.01/1.14    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))),
% 3.01/1.14    inference(ennf_transformation,[],[f14])).
% 3.01/1.14  
% 3.01/1.14  fof(f31,plain,(
% 3.01/1.14    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK2))),
% 3.01/1.14    introduced(choice_axiom,[])).
% 3.01/1.14  
% 3.01/1.14  fof(f32,plain,(
% 3.01/1.14    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK2))),
% 3.01/1.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f31])).
% 3.01/1.14  
% 3.01/1.14  fof(f55,plain,(
% 3.01/1.14    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK2))),
% 3.01/1.14    inference(cnf_transformation,[],[f32])).
% 3.01/1.14  
% 3.01/1.14  fof(f12,axiom,(
% 3.01/1.14    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0)),
% 3.01/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.14  
% 3.01/1.14  fof(f54,plain,(
% 3.01/1.14    ( ! [X0] : (k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0)) )),
% 3.01/1.14    inference(cnf_transformation,[],[f12])).
% 3.01/1.14  
% 3.01/1.14  fof(f61,plain,(
% 3.01/1.14    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK2)))),
% 3.01/1.14    inference(definition_unfolding,[],[f55,f54])).
% 3.01/1.14  
% 3.01/1.14  fof(f43,plain,(
% 3.01/1.14    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.01/1.14    inference(cnf_transformation,[],[f26])).
% 3.01/1.14  
% 3.01/1.14  cnf(c_14,plain,
% 3.01/1.14      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k9_setfam_1(X1)) ),
% 3.01/1.14      inference(cnf_transformation,[],[f67]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_8391,plain,
% 3.01/1.14      ( r1_tarski(X0,X1) != iProver_top
% 3.01/1.14      | r2_hidden(X0,k9_setfam_1(X1)) = iProver_top ),
% 3.01/1.14      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_19,plain,
% 3.01/1.14      ( ~ r2_hidden(k1_xboole_0,X0)
% 3.01/1.14      | v1_xboole_0(X0)
% 3.01/1.14      | k3_yellow_0(k2_yellow_1(X0)) = k1_xboole_0 ),
% 3.01/1.14      inference(cnf_transformation,[],[f53]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_7,plain,
% 3.01/1.14      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.01/1.14      inference(cnf_transformation,[],[f40]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_229,plain,
% 3.01/1.14      ( ~ r2_hidden(k1_xboole_0,X0)
% 3.01/1.14      | k3_yellow_0(k2_yellow_1(X0)) = k1_xboole_0
% 3.01/1.14      | k1_xboole_0 = X0 ),
% 3.01/1.14      inference(resolution,[status(thm)],[c_19,c_7]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_8386,plain,
% 3.01/1.14      ( k3_yellow_0(k2_yellow_1(X0)) = k1_xboole_0
% 3.01/1.14      | k1_xboole_0 = X0
% 3.01/1.14      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 3.01/1.14      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_8577,plain,
% 3.01/1.14      ( k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = k1_xboole_0
% 3.01/1.14      | k9_setfam_1(X0) = k1_xboole_0
% 3.01/1.14      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_8391,c_8386]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_10,plain,
% 3.01/1.14      ( r1_tarski(X0,X0) ),
% 3.01/1.14      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_42,plain,
% 3.01/1.14      ( r1_tarski(X0,X0) = iProver_top ),
% 3.01/1.14      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_44,plain,
% 3.01/1.14      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.01/1.14      inference(instantiation,[status(thm)],[c_42]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_3408,plain,
% 3.01/1.14      ( r1_tarski(X0,X0) = iProver_top ),
% 3.01/1.14      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_3407,plain,
% 3.01/1.14      ( r1_tarski(X0,X1) != iProver_top
% 3.01/1.14      | r2_hidden(X0,k9_setfam_1(X1)) = iProver_top ),
% 3.01/1.14      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_16,plain,
% 3.01/1.14      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
% 3.01/1.14      inference(cnf_transformation,[],[f49]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_3405,plain,
% 3.01/1.14      ( k2_xboole_0(k1_tarski(X0),X1) = X1
% 3.01/1.14      | r2_hidden(X0,X1) != iProver_top ),
% 3.01/1.14      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_3508,plain,
% 3.01/1.14      ( k2_xboole_0(k1_tarski(X0),k9_setfam_1(X1)) = k9_setfam_1(X1)
% 3.01/1.14      | r1_tarski(X0,X1) != iProver_top ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_3407,c_3405]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_3535,plain,
% 3.01/1.14      ( k2_xboole_0(k1_tarski(X0),k9_setfam_1(X0)) = k9_setfam_1(X0) ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_3408,c_3508]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_17,negated_conjecture,
% 3.01/1.14      ( k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
% 3.01/1.14      inference(cnf_transformation,[],[f50]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_3538,plain,
% 3.01/1.14      ( k9_setfam_1(X0) != k1_xboole_0 ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_3535,c_17]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_11,plain,
% 3.01/1.14      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.01/1.14      inference(cnf_transformation,[],[f44]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_0,plain,
% 3.01/1.14      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.01/1.14      inference(cnf_transformation,[],[f33]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_8472,plain,
% 3.01/1.14      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_18,plain,
% 3.01/1.14      ( k3_xboole_0(k9_setfam_1(X0),k9_setfam_1(X1)) = k9_setfam_1(k3_xboole_0(X0,X1)) ),
% 3.01/1.14      inference(cnf_transformation,[],[f60]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_8496,plain,
% 3.01/1.14      ( k3_xboole_0(k9_setfam_1(X0),k9_setfam_1(X1)) = k9_setfam_1(k3_xboole_0(X1,X0)) ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_0,c_18]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_8508,plain,
% 3.01/1.14      ( k9_setfam_1(k3_xboole_0(X0,X1)) = k9_setfam_1(k3_xboole_0(X1,X0)) ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_8496,c_18]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_8529,plain,
% 3.01/1.14      ( k3_xboole_0(k9_setfam_1(k3_xboole_0(X0,X1)),k9_setfam_1(X2)) = k9_setfam_1(k3_xboole_0(k3_xboole_0(X1,X0),X2)) ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_8508,c_18]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_9142,plain,
% 3.01/1.14      ( k9_setfam_1(k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = k3_xboole_0(k9_setfam_1(k1_xboole_0),k9_setfam_1(X1)) ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_8472,c_8529]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_9217,plain,
% 3.01/1.14      ( k3_xboole_0(k9_setfam_1(k1_xboole_0),k9_setfam_1(X0)) = k9_setfam_1(k3_xboole_0(k1_xboole_0,X0)) ),
% 3.01/1.14      inference(light_normalisation,[status(thm)],[c_9142,c_11]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_9218,plain,
% 3.01/1.14      ( k3_xboole_0(k9_setfam_1(k1_xboole_0),k9_setfam_1(X0)) = k9_setfam_1(k1_xboole_0) ),
% 3.01/1.14      inference(demodulation,[status(thm)],[c_9217,c_8472,c_8496]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_5,plain,
% 3.01/1.14      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.01/1.14      inference(cnf_transformation,[],[f63]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_8395,plain,
% 3.01/1.14      ( r2_hidden(X0,X1) = iProver_top
% 3.01/1.14      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 3.01/1.14      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_9853,plain,
% 3.01/1.14      ( r2_hidden(X0,k9_setfam_1(X1)) = iProver_top
% 3.01/1.14      | r2_hidden(X0,k9_setfam_1(k1_xboole_0)) != iProver_top ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_9218,c_8395]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_10294,plain,
% 3.01/1.14      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.01/1.14      | r2_hidden(X0,k9_setfam_1(X1)) = iProver_top ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_8391,c_9853]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_10317,plain,
% 3.01/1.14      ( k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = k1_xboole_0
% 3.01/1.14      | k9_setfam_1(X0) = k1_xboole_0
% 3.01/1.14      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.01/1.14      inference(superposition,[status(thm)],[c_10294,c_8386]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_14883,plain,
% 3.01/1.14      ( k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = k1_xboole_0 ),
% 3.01/1.14      inference(global_propositional_subsumption,
% 3.01/1.14                [status(thm)],
% 3.01/1.14                [c_8577,c_44,c_3538,c_10317]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_20,negated_conjecture,
% 3.01/1.14      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK2))) ),
% 3.01/1.14      inference(cnf_transformation,[],[f61]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_14886,plain,
% 3.01/1.14      ( k1_xboole_0 != k1_xboole_0 ),
% 3.01/1.14      inference(demodulation,[status(thm)],[c_14883,c_20]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_8,plain,
% 3.01/1.14      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.01/1.14      inference(cnf_transformation,[],[f43]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_47,plain,
% 3.01/1.14      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.01/1.14      | k1_xboole_0 = k1_xboole_0 ),
% 3.01/1.14      inference(instantiation,[status(thm)],[c_8]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(c_43,plain,
% 3.01/1.14      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.01/1.14      inference(instantiation,[status(thm)],[c_10]) ).
% 3.01/1.14  
% 3.01/1.14  cnf(contradiction,plain,
% 3.01/1.14      ( $false ),
% 3.01/1.14      inference(minisat,[status(thm)],[c_14886,c_47,c_43]) ).
% 3.01/1.14  
% 3.01/1.14  
% 3.01/1.14  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.14  
% 3.01/1.14  ------                               Statistics
% 3.01/1.14  
% 3.01/1.14  ------ Selected
% 3.01/1.14  
% 3.01/1.14  total_time:                             0.308
% 3.01/1.14  
%------------------------------------------------------------------------------
