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
% DateTime   : Thu Dec  3 11:43:54 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 363 expanded)
%              Number of clauses        :   36 (  53 expanded)
%              Number of leaves         :   21 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  225 ( 633 expanded)
%              Number of equality atoms :  135 ( 421 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f55])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f32,f58])).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f33,f59])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f44,f59,f60])).

fof(f67,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))))) ),
    inference(equality_resolution,[],[f63])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK3(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f30])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f19,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
    | r2_hidden(sK0(X0,X1),X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_332,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_335,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_598,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_335])).

cnf(c_653,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_332,c_598])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(sK3(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_328,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1182,plain,
    ( k1_relat_1(X0) = k2_relat_1(k1_xboole_0)
    | r2_hidden(sK3(X0),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_653,c_328])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_330,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_603,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_330,c_598])).

cnf(c_2551,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1182,c_603])).

cnf(c_1184,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_598])).

cnf(c_138,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_491,plain,
    ( k1_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_838,plain,
    ( k1_relat_1(k1_xboole_0) != k2_relat_1(X0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_839,plain,
    ( k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_409,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_410,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_146,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_400,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_401,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_403,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_401])).

cnf(c_379,plain,
    ( k2_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_380,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_42,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_41,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_19,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2551,c_1184,c_839,c_410,c_403,c_380,c_42,c_41,c_19,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:58:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.40/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/0.99  
% 3.40/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/0.99  
% 3.40/0.99  ------  iProver source info
% 3.40/0.99  
% 3.40/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.40/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/0.99  git: non_committed_changes: false
% 3.40/0.99  git: last_make_outside_of_git: false
% 3.40/0.99  
% 3.40/0.99  ------ 
% 3.40/0.99  ------ Parsing...
% 3.40/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/0.99  
% 3.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.40/0.99  
% 3.40/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/0.99  
% 3.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/0.99  ------ Proving...
% 3.40/0.99  ------ Problem Properties 
% 3.40/0.99  
% 3.40/0.99  
% 3.40/0.99  clauses                                 14
% 3.40/0.99  conjectures                             1
% 3.40/0.99  EPR                                     0
% 3.40/0.99  Horn                                    11
% 3.40/0.99  unary                                   5
% 3.40/0.99  binary                                  4
% 3.40/0.99  lits                                    28
% 3.40/0.99  lits eq                                 11
% 3.40/0.99  fd_pure                                 0
% 3.40/0.99  fd_pseudo                               0
% 3.40/0.99  fd_cond                                 1
% 3.40/0.99  fd_pseudo_cond                          3
% 3.40/0.99  AC symbols                              0
% 3.40/0.99  
% 3.40/0.99  ------ Input Options Time Limit: Unbounded
% 3.40/0.99  
% 3.40/0.99  
% 3.40/0.99  ------ 
% 3.40/0.99  Current options:
% 3.40/0.99  ------ 
% 3.40/0.99  
% 3.40/0.99  
% 3.40/0.99  
% 3.40/0.99  
% 3.40/0.99  ------ Proving...
% 3.40/0.99  
% 3.40/0.99  
% 3.40/0.99  % SZS status Theorem for theBenchmark.p
% 3.40/0.99  
% 3.40/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/0.99  
% 3.40/0.99  fof(f12,axiom,(
% 3.40/0.99    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f24,plain,(
% 3.40/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.40/0.99    inference(nnf_transformation,[],[f12])).
% 3.40/0.99  
% 3.40/0.99  fof(f25,plain,(
% 3.40/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.40/0.99    inference(rectify,[],[f24])).
% 3.40/0.99  
% 3.40/0.99  fof(f28,plain,(
% 3.40/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0))),
% 3.40/0.99    introduced(choice_axiom,[])).
% 3.40/0.99  
% 3.40/0.99  fof(f27,plain,(
% 3.40/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0))) )),
% 3.40/0.99    introduced(choice_axiom,[])).
% 3.40/0.99  
% 3.40/0.99  fof(f26,plain,(
% 3.40/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.40/0.99    introduced(choice_axiom,[])).
% 3.40/0.99  
% 3.40/0.99  fof(f29,plain,(
% 3.40/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).
% 3.40/0.99  
% 3.40/0.99  fof(f49,plain,(
% 3.40/0.99    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)) )),
% 3.40/0.99    inference(cnf_transformation,[],[f29])).
% 3.40/0.99  
% 3.40/0.99  fof(f2,axiom,(
% 3.40/0.99    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f33,plain,(
% 3.40/0.99    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 3.40/0.99    inference(cnf_transformation,[],[f2])).
% 3.40/0.99  
% 3.40/0.99  fof(f1,axiom,(
% 3.40/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f32,plain,(
% 3.40/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.40/0.99    inference(cnf_transformation,[],[f1])).
% 3.40/0.99  
% 3.40/0.99  fof(f11,axiom,(
% 3.40/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f46,plain,(
% 3.40/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.40/0.99    inference(cnf_transformation,[],[f11])).
% 3.40/0.99  
% 3.40/0.99  fof(f4,axiom,(
% 3.40/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f35,plain,(
% 3.40/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.40/0.99    inference(cnf_transformation,[],[f4])).
% 3.40/0.99  
% 3.40/0.99  fof(f5,axiom,(
% 3.40/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f36,plain,(
% 3.40/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.40/0.99    inference(cnf_transformation,[],[f5])).
% 3.40/0.99  
% 3.40/0.99  fof(f6,axiom,(
% 3.40/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f37,plain,(
% 3.40/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.40/0.99    inference(cnf_transformation,[],[f6])).
% 3.40/0.99  
% 3.40/0.99  fof(f7,axiom,(
% 3.40/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f38,plain,(
% 3.40/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.40/0.99    inference(cnf_transformation,[],[f7])).
% 3.40/0.99  
% 3.40/0.99  fof(f8,axiom,(
% 3.40/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f39,plain,(
% 3.40/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.40/0.99    inference(cnf_transformation,[],[f8])).
% 3.40/0.99  
% 3.40/0.99  fof(f54,plain,(
% 3.40/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.40/0.99    inference(definition_unfolding,[],[f38,f39])).
% 3.40/0.99  
% 3.40/0.99  fof(f55,plain,(
% 3.40/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.40/0.99    inference(definition_unfolding,[],[f37,f54])).
% 3.40/0.99  
% 3.40/0.99  fof(f56,plain,(
% 3.40/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.40/0.99    inference(definition_unfolding,[],[f36,f55])).
% 3.40/0.99  
% 3.40/0.99  fof(f57,plain,(
% 3.40/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.40/0.99    inference(definition_unfolding,[],[f35,f56])).
% 3.40/0.99  
% 3.40/0.99  fof(f58,plain,(
% 3.40/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.40/0.99    inference(definition_unfolding,[],[f46,f57])).
% 3.40/0.99  
% 3.40/0.99  fof(f59,plain,(
% 3.40/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.40/0.99    inference(definition_unfolding,[],[f32,f58])).
% 3.40/0.99  
% 3.40/0.99  fof(f61,plain,(
% 3.40/0.99    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0) )),
% 3.40/0.99    inference(definition_unfolding,[],[f33,f59])).
% 3.40/0.99  
% 3.40/0.99  fof(f10,axiom,(
% 3.40/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f22,plain,(
% 3.40/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.40/0.99    inference(nnf_transformation,[],[f10])).
% 3.40/0.99  
% 3.40/0.99  fof(f23,plain,(
% 3.40/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.40/0.99    inference(flattening,[],[f22])).
% 3.40/0.99  
% 3.40/0.99  fof(f44,plain,(
% 3.40/0.99    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.40/0.99    inference(cnf_transformation,[],[f23])).
% 3.40/0.99  
% 3.40/0.99  fof(f3,axiom,(
% 3.40/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f34,plain,(
% 3.40/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.40/0.99    inference(cnf_transformation,[],[f3])).
% 3.40/0.99  
% 3.40/0.99  fof(f60,plain,(
% 3.40/0.99    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.40/0.99    inference(definition_unfolding,[],[f34,f57])).
% 3.40/0.99  
% 3.40/0.99  fof(f63,plain,(
% 3.40/0.99    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))))) )),
% 3.40/0.99    inference(definition_unfolding,[],[f44,f59,f60])).
% 3.40/0.99  
% 3.40/0.99  fof(f67,plain,(
% 3.40/0.99    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))))) )),
% 3.40/0.99    inference(equality_resolution,[],[f63])).
% 3.40/0.99  
% 3.40/0.99  fof(f14,axiom,(
% 3.40/0.99    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f17,plain,(
% 3.40/0.99    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.40/0.99    inference(ennf_transformation,[],[f14])).
% 3.40/0.99  
% 3.40/0.99  fof(f18,plain,(
% 3.40/0.99    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.40/0.99    inference(flattening,[],[f17])).
% 3.40/0.99  
% 3.40/0.99  fof(f30,plain,(
% 3.40/0.99    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK3(X1),k2_relat_1(X1)))),
% 3.40/0.99    introduced(choice_axiom,[])).
% 3.40/0.99  
% 3.40/0.99  fof(f31,plain,(
% 3.40/0.99    ! [X0,X1] : (r2_hidden(sK3(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f30])).
% 3.40/0.99  
% 3.40/0.99  fof(f52,plain,(
% 3.40/0.99    ( ! [X0,X1] : (r2_hidden(sK3(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.40/0.99    inference(cnf_transformation,[],[f31])).
% 3.40/0.99  
% 3.40/0.99  fof(f47,plain,(
% 3.40/0.99    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.40/0.99    inference(cnf_transformation,[],[f29])).
% 3.40/0.99  
% 3.40/0.99  fof(f69,plain,(
% 3.40/0.99    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.40/0.99    inference(equality_resolution,[],[f47])).
% 3.40/0.99  
% 3.40/0.99  fof(f9,axiom,(
% 3.40/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f20,plain,(
% 3.40/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.40/0.99    inference(nnf_transformation,[],[f9])).
% 3.40/0.99  
% 3.40/0.99  fof(f21,plain,(
% 3.40/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.40/0.99    inference(flattening,[],[f20])).
% 3.40/0.99  
% 3.40/0.99  fof(f41,plain,(
% 3.40/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.40/0.99    inference(cnf_transformation,[],[f21])).
% 3.40/0.99  
% 3.40/0.99  fof(f66,plain,(
% 3.40/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.40/0.99    inference(equality_resolution,[],[f41])).
% 3.40/0.99  
% 3.40/0.99  fof(f40,plain,(
% 3.40/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.40/0.99    inference(cnf_transformation,[],[f21])).
% 3.40/0.99  
% 3.40/0.99  fof(f13,axiom,(
% 3.40/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f51,plain,(
% 3.40/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.40/0.99    inference(cnf_transformation,[],[f13])).
% 3.40/0.99  
% 3.40/0.99  fof(f15,conjecture,(
% 3.40/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.99  
% 3.40/0.99  fof(f16,negated_conjecture,(
% 3.40/0.99    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 3.40/0.99    inference(negated_conjecture,[],[f15])).
% 3.40/0.99  
% 3.40/0.99  fof(f19,plain,(
% 3.40/0.99    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 3.40/0.99    inference(ennf_transformation,[],[f16])).
% 3.40/0.99  
% 3.40/0.99  fof(f53,plain,(
% 3.40/0.99    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 3.40/0.99    inference(cnf_transformation,[],[f19])).
% 3.40/0.99  
% 3.40/0.99  cnf(c_8,plain,
% 3.40/0.99      ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
% 3.40/0.99      | r2_hidden(sK0(X0,X1),X1)
% 3.40/0.99      | k2_relat_1(X0) = X1 ),
% 3.40/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_332,plain,
% 3.40/0.99      ( k2_relat_1(X0) = X1
% 3.40/0.99      | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) = iProver_top
% 3.40/0.99      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 3.40/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_0,plain,
% 3.40/0.99      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
% 3.40/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_5,plain,
% 3.40/0.99      ( ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) ),
% 3.40/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_335,plain,
% 3.40/0.99      ( r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) != iProver_top ),
% 3.40/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_598,plain,
% 3.40/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.40/0.99      inference(superposition,[status(thm)],[c_0,c_335]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_653,plain,
% 3.40/0.99      ( k2_relat_1(k1_xboole_0) = X0
% 3.40/0.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 3.40/0.99      inference(superposition,[status(thm)],[c_332,c_598]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_12,plain,
% 3.40/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.40/0.99      | r2_hidden(sK3(X1),k2_relat_1(X1))
% 3.40/0.99      | ~ v1_relat_1(X1) ),
% 3.40/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_328,plain,
% 3.40/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.40/0.99      | r2_hidden(sK3(X1),k2_relat_1(X1)) = iProver_top
% 3.40/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.40/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_1182,plain,
% 3.40/0.99      ( k1_relat_1(X0) = k2_relat_1(k1_xboole_0)
% 3.40/0.99      | r2_hidden(sK3(X0),k2_relat_1(X0)) = iProver_top
% 3.40/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.99      inference(superposition,[status(thm)],[c_653,c_328]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_10,plain,
% 3.40/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.40/0.99      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
% 3.40/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_330,plain,
% 3.40/0.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.40/0.99      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
% 3.40/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_603,plain,
% 3.40/0.99      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 3.40/0.99      inference(superposition,[status(thm)],[c_330,c_598]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_2551,plain,
% 3.40/0.99      ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)
% 3.40/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.40/0.99      inference(superposition,[status(thm)],[c_1182,c_603]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_1184,plain,
% 3.40/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.40/0.99      inference(superposition,[status(thm)],[c_653,c_598]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_138,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_491,plain,
% 3.40/0.99      ( k1_relat_1(k1_xboole_0) != X0
% 3.40/0.99      | k1_xboole_0 != X0
% 3.40/0.99      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_138]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_838,plain,
% 3.40/0.99      ( k1_relat_1(k1_xboole_0) != k2_relat_1(X0)
% 3.40/0.99      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 3.40/0.99      | k1_xboole_0 != k2_relat_1(X0) ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_491]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_839,plain,
% 3.40/0.99      ( k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
% 3.40/0.99      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 3.40/0.99      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_838]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_409,plain,
% 3.40/0.99      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_138]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_410,plain,
% 3.40/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.40/0.99      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.40/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_409]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_146,plain,
% 3.40/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.40/0.99      theory(equality) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_400,plain,
% 3.40/0.99      ( v1_relat_1(X0)
% 3.40/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
% 3.40/0.99      | X0 != k2_zfmisc_1(X1,X2) ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_146]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_401,plain,
% 3.40/0.99      ( X0 != k2_zfmisc_1(X1,X2)
% 3.40/0.99      | v1_relat_1(X0) = iProver_top
% 3.40/0.99      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.40/0.99      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_403,plain,
% 3.40/0.99      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.40/0.99      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.40/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_401]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_379,plain,
% 3.40/0.99      ( k2_relat_1(k1_xboole_0) != X0
% 3.40/0.99      | k1_xboole_0 != X0
% 3.40/0.99      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_138]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_380,plain,
% 3.40/0.99      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 3.40/0.99      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 3.40/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_379]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_2,plain,
% 3.40/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.40/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_42,plain,
% 3.40/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_3,plain,
% 3.40/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.40/0.99      | k1_xboole_0 = X1
% 3.40/0.99      | k1_xboole_0 = X0 ),
% 3.40/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_41,plain,
% 3.40/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.40/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_11,plain,
% 3.40/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.40/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_17,plain,
% 3.40/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.40/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_19,plain,
% 3.40/0.99      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.40/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(c_13,negated_conjecture,
% 3.40/0.99      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
% 3.40/0.99      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 3.40/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.40/0.99  
% 3.40/0.99  cnf(contradiction,plain,
% 3.40/0.99      ( $false ),
% 3.40/0.99      inference(minisat,
% 3.40/0.99                [status(thm)],
% 3.40/0.99                [c_2551,c_1184,c_839,c_410,c_403,c_380,c_42,c_41,c_19,
% 3.40/0.99                 c_13]) ).
% 3.40/0.99  
% 3.40/0.99  
% 3.40/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/0.99  
% 3.40/0.99  ------                               Statistics
% 3.40/0.99  
% 3.40/0.99  ------ Selected
% 3.40/0.99  
% 3.40/0.99  total_time:                             0.127
% 3.40/0.99  
%------------------------------------------------------------------------------
