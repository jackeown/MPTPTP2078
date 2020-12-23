%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:11 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 236 expanded)
%              Number of clauses        :   50 (  78 expanded)
%              Number of leaves         :   17 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  225 ( 456 expanded)
%              Number of equality atoms :  152 ( 297 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f26,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f29])).

fof(f49,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f56,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f32,f54])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f40])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f50,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_259,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_266,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_264,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_752,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_266,c_264])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_263,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_262,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_839,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_263,c_262])).

cnf(c_1484,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_752,c_839])).

cnf(c_7933,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_259,c_1484])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_260,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_405,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_260])).

cnf(c_11,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_419,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_405,c_11])).

cnf(c_28,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_30,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_37,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_853,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_30,c_37])).

cnf(c_854,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_853])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_265,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_860,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_854,c_265])).

cnf(c_865,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_259,c_860])).

cnf(c_7940,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7933,c_865])).

cnf(c_1,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7941,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7940,c_1,c_3])).

cnf(c_1483,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0))))) = k5_relat_1(X0,sK0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_259,c_839])).

cnf(c_7533,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_752,c_1483])).

cnf(c_9,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_261,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_652,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_261])).

cnf(c_666,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_652,c_12])).

cnf(c_954,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_666,c_30,c_37])).

cnf(c_955,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_954])).

cnf(c_961,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_955,c_265])).

cnf(c_966,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_259,c_961])).

cnf(c_7535,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_7533,c_966])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7536,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7535,c_1,c_4])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7642,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7536,c_13])).

cnf(c_7643,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7642])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7941,c_7643])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 18:15:37 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 3.87/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.03  
% 3.87/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/1.03  
% 3.87/1.03  ------  iProver source info
% 3.87/1.03  
% 3.87/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.87/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/1.03  git: non_committed_changes: false
% 3.87/1.03  git: last_make_outside_of_git: false
% 3.87/1.03  
% 3.87/1.03  ------ 
% 3.87/1.03  
% 3.87/1.03  ------ Input Options
% 3.87/1.03  
% 3.87/1.03  --out_options                           all
% 3.87/1.03  --tptp_safe_out                         true
% 3.87/1.03  --problem_path                          ""
% 3.87/1.03  --include_path                          ""
% 3.87/1.03  --clausifier                            res/vclausify_rel
% 3.87/1.03  --clausifier_options                    --mode clausify
% 3.87/1.03  --stdin                                 false
% 3.87/1.03  --stats_out                             sel
% 3.87/1.03  
% 3.87/1.03  ------ General Options
% 3.87/1.03  
% 3.87/1.03  --fof                                   false
% 3.87/1.03  --time_out_real                         604.98
% 3.87/1.03  --time_out_virtual                      -1.
% 3.87/1.03  --symbol_type_check                     false
% 3.87/1.03  --clausify_out                          false
% 3.87/1.03  --sig_cnt_out                           false
% 3.87/1.03  --trig_cnt_out                          false
% 3.87/1.03  --trig_cnt_out_tolerance                1.
% 3.87/1.03  --trig_cnt_out_sk_spl                   false
% 3.87/1.03  --abstr_cl_out                          false
% 3.87/1.03  
% 3.87/1.03  ------ Global Options
% 3.87/1.03  
% 3.87/1.03  --schedule                              none
% 3.87/1.03  --add_important_lit                     false
% 3.87/1.03  --prop_solver_per_cl                    1000
% 3.87/1.03  --min_unsat_core                        false
% 3.87/1.03  --soft_assumptions                      false
% 3.87/1.03  --soft_lemma_size                       3
% 3.87/1.03  --prop_impl_unit_size                   0
% 3.87/1.03  --prop_impl_unit                        []
% 3.87/1.03  --share_sel_clauses                     true
% 3.87/1.03  --reset_solvers                         false
% 3.87/1.03  --bc_imp_inh                            [conj_cone]
% 3.87/1.03  --conj_cone_tolerance                   3.
% 3.87/1.03  --extra_neg_conj                        none
% 3.87/1.03  --large_theory_mode                     true
% 3.87/1.03  --prolific_symb_bound                   200
% 3.87/1.03  --lt_threshold                          2000
% 3.87/1.03  --clause_weak_htbl                      true
% 3.87/1.03  --gc_record_bc_elim                     false
% 3.87/1.03  
% 3.87/1.03  ------ Preprocessing Options
% 3.87/1.03  
% 3.87/1.03  --preprocessing_flag                    true
% 3.87/1.03  --time_out_prep_mult                    0.1
% 3.87/1.03  --splitting_mode                        input
% 3.87/1.03  --splitting_grd                         true
% 3.87/1.03  --splitting_cvd                         false
% 3.87/1.03  --splitting_cvd_svl                     false
% 3.87/1.03  --splitting_nvd                         32
% 3.87/1.03  --sub_typing                            true
% 3.87/1.03  --prep_gs_sim                           false
% 3.87/1.03  --prep_unflatten                        true
% 3.87/1.03  --prep_res_sim                          true
% 3.87/1.03  --prep_upred                            true
% 3.87/1.03  --prep_sem_filter                       exhaustive
% 3.87/1.03  --prep_sem_filter_out                   false
% 3.87/1.03  --pred_elim                             false
% 3.87/1.03  --res_sim_input                         true
% 3.87/1.03  --eq_ax_congr_red                       true
% 3.87/1.03  --pure_diseq_elim                       true
% 3.87/1.03  --brand_transform                       false
% 3.87/1.03  --non_eq_to_eq                          false
% 3.87/1.03  --prep_def_merge                        true
% 3.87/1.03  --prep_def_merge_prop_impl              false
% 3.87/1.03  --prep_def_merge_mbd                    true
% 3.87/1.03  --prep_def_merge_tr_red                 false
% 3.87/1.03  --prep_def_merge_tr_cl                  false
% 3.87/1.03  --smt_preprocessing                     true
% 3.87/1.03  --smt_ac_axioms                         fast
% 3.87/1.03  --preprocessed_out                      false
% 3.87/1.03  --preprocessed_stats                    false
% 3.87/1.03  
% 3.87/1.03  ------ Abstraction refinement Options
% 3.87/1.03  
% 3.87/1.03  --abstr_ref                             []
% 3.87/1.03  --abstr_ref_prep                        false
% 3.87/1.03  --abstr_ref_until_sat                   false
% 3.87/1.03  --abstr_ref_sig_restrict                funpre
% 3.87/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/1.03  --abstr_ref_under                       []
% 3.87/1.03  
% 3.87/1.03  ------ SAT Options
% 3.87/1.03  
% 3.87/1.03  --sat_mode                              false
% 3.87/1.03  --sat_fm_restart_options                ""
% 3.87/1.03  --sat_gr_def                            false
% 3.87/1.03  --sat_epr_types                         true
% 3.87/1.03  --sat_non_cyclic_types                  false
% 3.87/1.03  --sat_finite_models                     false
% 3.87/1.03  --sat_fm_lemmas                         false
% 3.87/1.03  --sat_fm_prep                           false
% 3.87/1.03  --sat_fm_uc_incr                        true
% 3.87/1.03  --sat_out_model                         small
% 3.87/1.03  --sat_out_clauses                       false
% 3.87/1.03  
% 3.87/1.03  ------ QBF Options
% 3.87/1.03  
% 3.87/1.03  --qbf_mode                              false
% 3.87/1.03  --qbf_elim_univ                         false
% 3.87/1.03  --qbf_dom_inst                          none
% 3.87/1.03  --qbf_dom_pre_inst                      false
% 3.87/1.03  --qbf_sk_in                             false
% 3.87/1.03  --qbf_pred_elim                         true
% 3.87/1.03  --qbf_split                             512
% 3.87/1.03  
% 3.87/1.03  ------ BMC1 Options
% 3.87/1.03  
% 3.87/1.03  --bmc1_incremental                      false
% 3.87/1.03  --bmc1_axioms                           reachable_all
% 3.87/1.03  --bmc1_min_bound                        0
% 3.87/1.03  --bmc1_max_bound                        -1
% 3.87/1.03  --bmc1_max_bound_default                -1
% 3.87/1.03  --bmc1_symbol_reachability              true
% 3.87/1.03  --bmc1_property_lemmas                  false
% 3.87/1.03  --bmc1_k_induction                      false
% 3.87/1.03  --bmc1_non_equiv_states                 false
% 3.87/1.03  --bmc1_deadlock                         false
% 3.87/1.03  --bmc1_ucm                              false
% 3.87/1.03  --bmc1_add_unsat_core                   none
% 3.87/1.03  --bmc1_unsat_core_children              false
% 3.87/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/1.03  --bmc1_out_stat                         full
% 3.87/1.03  --bmc1_ground_init                      false
% 3.87/1.03  --bmc1_pre_inst_next_state              false
% 3.87/1.03  --bmc1_pre_inst_state                   false
% 3.87/1.03  --bmc1_pre_inst_reach_state             false
% 3.87/1.03  --bmc1_out_unsat_core                   false
% 3.87/1.03  --bmc1_aig_witness_out                  false
% 3.87/1.03  --bmc1_verbose                          false
% 3.87/1.03  --bmc1_dump_clauses_tptp                false
% 3.87/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.87/1.03  --bmc1_dump_file                        -
% 3.87/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.87/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.87/1.03  --bmc1_ucm_extend_mode                  1
% 3.87/1.03  --bmc1_ucm_init_mode                    2
% 3.87/1.03  --bmc1_ucm_cone_mode                    none
% 3.87/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.87/1.03  --bmc1_ucm_relax_model                  4
% 3.87/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.87/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/1.03  --bmc1_ucm_layered_model                none
% 3.87/1.03  --bmc1_ucm_max_lemma_size               10
% 3.87/1.03  
% 3.87/1.03  ------ AIG Options
% 3.87/1.03  
% 3.87/1.03  --aig_mode                              false
% 3.87/1.03  
% 3.87/1.03  ------ Instantiation Options
% 3.87/1.03  
% 3.87/1.03  --instantiation_flag                    true
% 3.87/1.03  --inst_sos_flag                         false
% 3.87/1.03  --inst_sos_phase                        true
% 3.87/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/1.03  --inst_lit_sel_side                     num_symb
% 3.87/1.03  --inst_solver_per_active                1400
% 3.87/1.03  --inst_solver_calls_frac                1.
% 3.87/1.03  --inst_passive_queue_type               priority_queues
% 3.87/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/1.03  --inst_passive_queues_freq              [25;2]
% 3.87/1.03  --inst_dismatching                      true
% 3.87/1.03  --inst_eager_unprocessed_to_passive     true
% 3.87/1.03  --inst_prop_sim_given                   true
% 3.87/1.03  --inst_prop_sim_new                     false
% 3.87/1.03  --inst_subs_new                         false
% 3.87/1.03  --inst_eq_res_simp                      false
% 3.87/1.03  --inst_subs_given                       false
% 3.87/1.03  --inst_orphan_elimination               true
% 3.87/1.03  --inst_learning_loop_flag               true
% 3.87/1.03  --inst_learning_start                   3000
% 3.87/1.03  --inst_learning_factor                  2
% 3.87/1.03  --inst_start_prop_sim_after_learn       3
% 3.87/1.03  --inst_sel_renew                        solver
% 3.87/1.03  --inst_lit_activity_flag                true
% 3.87/1.03  --inst_restr_to_given                   false
% 3.87/1.03  --inst_activity_threshold               500
% 3.87/1.03  --inst_out_proof                        true
% 3.87/1.03  
% 3.87/1.03  ------ Resolution Options
% 3.87/1.03  
% 3.87/1.03  --resolution_flag                       true
% 3.87/1.03  --res_lit_sel                           adaptive
% 3.87/1.03  --res_lit_sel_side                      none
% 3.87/1.03  --res_ordering                          kbo
% 3.87/1.03  --res_to_prop_solver                    active
% 3.87/1.03  --res_prop_simpl_new                    false
% 3.87/1.03  --res_prop_simpl_given                  true
% 3.87/1.03  --res_passive_queue_type                priority_queues
% 3.87/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/1.03  --res_passive_queues_freq               [15;5]
% 3.87/1.03  --res_forward_subs                      full
% 3.87/1.03  --res_backward_subs                     full
% 3.87/1.03  --res_forward_subs_resolution           true
% 3.87/1.03  --res_backward_subs_resolution          true
% 3.87/1.03  --res_orphan_elimination                true
% 3.87/1.03  --res_time_limit                        2.
% 3.87/1.03  --res_out_proof                         true
% 3.87/1.03  
% 3.87/1.03  ------ Superposition Options
% 3.87/1.03  
% 3.87/1.03  --superposition_flag                    true
% 3.87/1.03  --sup_passive_queue_type                priority_queues
% 3.87/1.03  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/1.03  --sup_passive_queues_freq               [1;4]
% 3.87/1.03  --demod_completeness_check              fast
% 3.87/1.03  --demod_use_ground                      true
% 3.87/1.03  --sup_to_prop_solver                    passive
% 3.87/1.03  --sup_prop_simpl_new                    true
% 3.87/1.03  --sup_prop_simpl_given                  true
% 3.87/1.03  --sup_fun_splitting                     false
% 3.87/1.03  --sup_smt_interval                      50000
% 3.87/1.03  
% 3.87/1.03  ------ Superposition Simplification Setup
% 3.87/1.03  
% 3.87/1.03  --sup_indices_passive                   []
% 3.87/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.03  --sup_full_bw                           [BwDemod]
% 3.87/1.03  --sup_immed_triv                        [TrivRules]
% 3.87/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.03  --sup_immed_bw_main                     []
% 3.87/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.03  
% 3.87/1.03  ------ Combination Options
% 3.87/1.03  
% 3.87/1.03  --comb_res_mult                         3
% 3.87/1.03  --comb_sup_mult                         2
% 3.87/1.03  --comb_inst_mult                        10
% 3.87/1.03  
% 3.87/1.03  ------ Debug Options
% 3.87/1.03  
% 3.87/1.03  --dbg_backtrace                         false
% 3.87/1.03  --dbg_dump_prop_clauses                 false
% 3.87/1.03  --dbg_dump_prop_clauses_file            -
% 3.87/1.03  --dbg_out_stat                          false
% 3.87/1.03  ------ Parsing...
% 3.87/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/1.03  
% 3.87/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.87/1.03  
% 3.87/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/1.03  
% 3.87/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/1.03  ------ Proving...
% 3.87/1.03  ------ Problem Properties 
% 3.87/1.03  
% 3.87/1.03  
% 3.87/1.03  clauses                                 15
% 3.87/1.03  conjectures                             2
% 3.87/1.03  EPR                                     4
% 3.87/1.03  Horn                                    14
% 3.87/1.03  unary                                   8
% 3.87/1.03  binary                                  3
% 3.87/1.03  lits                                    28
% 3.87/1.03  lits eq                                 13
% 3.87/1.03  fd_pure                                 0
% 3.87/1.03  fd_pseudo                               0
% 3.87/1.03  fd_cond                                 1
% 3.87/1.03  fd_pseudo_cond                          0
% 3.87/1.03  AC symbols                              0
% 3.87/1.03  
% 3.87/1.03  ------ Input Options Time Limit: Unbounded
% 3.87/1.03  
% 3.87/1.03  
% 3.87/1.03  ------ 
% 3.87/1.03  Current options:
% 3.87/1.03  ------ 
% 3.87/1.03  
% 3.87/1.03  ------ Input Options
% 3.87/1.03  
% 3.87/1.03  --out_options                           all
% 3.87/1.03  --tptp_safe_out                         true
% 3.87/1.03  --problem_path                          ""
% 3.87/1.03  --include_path                          ""
% 3.87/1.03  --clausifier                            res/vclausify_rel
% 3.87/1.03  --clausifier_options                    --mode clausify
% 3.87/1.03  --stdin                                 false
% 3.87/1.03  --stats_out                             sel
% 3.87/1.03  
% 3.87/1.03  ------ General Options
% 3.87/1.03  
% 3.87/1.03  --fof                                   false
% 3.87/1.03  --time_out_real                         604.98
% 3.87/1.03  --time_out_virtual                      -1.
% 3.87/1.03  --symbol_type_check                     false
% 3.87/1.03  --clausify_out                          false
% 3.87/1.03  --sig_cnt_out                           false
% 3.87/1.03  --trig_cnt_out                          false
% 3.87/1.03  --trig_cnt_out_tolerance                1.
% 3.87/1.03  --trig_cnt_out_sk_spl                   false
% 3.87/1.03  --abstr_cl_out                          false
% 3.87/1.03  
% 3.87/1.03  ------ Global Options
% 3.87/1.03  
% 3.87/1.03  --schedule                              none
% 3.87/1.03  --add_important_lit                     false
% 3.87/1.03  --prop_solver_per_cl                    1000
% 3.87/1.03  --min_unsat_core                        false
% 3.87/1.03  --soft_assumptions                      false
% 3.87/1.03  --soft_lemma_size                       3
% 3.87/1.03  --prop_impl_unit_size                   0
% 3.87/1.03  --prop_impl_unit                        []
% 3.87/1.03  --share_sel_clauses                     true
% 3.87/1.03  --reset_solvers                         false
% 3.87/1.03  --bc_imp_inh                            [conj_cone]
% 3.87/1.03  --conj_cone_tolerance                   3.
% 3.87/1.03  --extra_neg_conj                        none
% 3.87/1.03  --large_theory_mode                     true
% 3.87/1.03  --prolific_symb_bound                   200
% 3.87/1.03  --lt_threshold                          2000
% 3.87/1.03  --clause_weak_htbl                      true
% 3.87/1.03  --gc_record_bc_elim                     false
% 3.87/1.03  
% 3.87/1.03  ------ Preprocessing Options
% 3.87/1.03  
% 3.87/1.03  --preprocessing_flag                    true
% 3.87/1.03  --time_out_prep_mult                    0.1
% 3.87/1.03  --splitting_mode                        input
% 3.87/1.03  --splitting_grd                         true
% 3.87/1.03  --splitting_cvd                         false
% 3.87/1.03  --splitting_cvd_svl                     false
% 3.87/1.03  --splitting_nvd                         32
% 3.87/1.03  --sub_typing                            true
% 3.87/1.03  --prep_gs_sim                           false
% 3.87/1.03  --prep_unflatten                        true
% 3.87/1.03  --prep_res_sim                          true
% 3.87/1.03  --prep_upred                            true
% 3.87/1.03  --prep_sem_filter                       exhaustive
% 3.87/1.03  --prep_sem_filter_out                   false
% 3.87/1.03  --pred_elim                             false
% 3.87/1.03  --res_sim_input                         true
% 3.87/1.03  --eq_ax_congr_red                       true
% 3.87/1.03  --pure_diseq_elim                       true
% 3.87/1.03  --brand_transform                       false
% 3.87/1.03  --non_eq_to_eq                          false
% 3.87/1.03  --prep_def_merge                        true
% 3.87/1.03  --prep_def_merge_prop_impl              false
% 3.87/1.03  --prep_def_merge_mbd                    true
% 3.87/1.03  --prep_def_merge_tr_red                 false
% 3.87/1.03  --prep_def_merge_tr_cl                  false
% 3.87/1.03  --smt_preprocessing                     true
% 3.87/1.03  --smt_ac_axioms                         fast
% 3.87/1.03  --preprocessed_out                      false
% 3.87/1.03  --preprocessed_stats                    false
% 3.87/1.03  
% 3.87/1.03  ------ Abstraction refinement Options
% 3.87/1.03  
% 3.87/1.03  --abstr_ref                             []
% 3.87/1.03  --abstr_ref_prep                        false
% 3.87/1.03  --abstr_ref_until_sat                   false
% 3.87/1.03  --abstr_ref_sig_restrict                funpre
% 3.87/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/1.03  --abstr_ref_under                       []
% 3.87/1.03  
% 3.87/1.03  ------ SAT Options
% 3.87/1.03  
% 3.87/1.03  --sat_mode                              false
% 3.87/1.03  --sat_fm_restart_options                ""
% 3.87/1.03  --sat_gr_def                            false
% 3.87/1.03  --sat_epr_types                         true
% 3.87/1.03  --sat_non_cyclic_types                  false
% 3.87/1.03  --sat_finite_models                     false
% 3.87/1.03  --sat_fm_lemmas                         false
% 3.87/1.03  --sat_fm_prep                           false
% 3.87/1.03  --sat_fm_uc_incr                        true
% 3.87/1.03  --sat_out_model                         small
% 3.87/1.03  --sat_out_clauses                       false
% 3.87/1.03  
% 3.87/1.03  ------ QBF Options
% 3.87/1.03  
% 3.87/1.03  --qbf_mode                              false
% 3.87/1.03  --qbf_elim_univ                         false
% 3.87/1.03  --qbf_dom_inst                          none
% 3.87/1.03  --qbf_dom_pre_inst                      false
% 3.87/1.03  --qbf_sk_in                             false
% 3.87/1.03  --qbf_pred_elim                         true
% 3.87/1.03  --qbf_split                             512
% 3.87/1.03  
% 3.87/1.03  ------ BMC1 Options
% 3.87/1.03  
% 3.87/1.03  --bmc1_incremental                      false
% 3.87/1.03  --bmc1_axioms                           reachable_all
% 3.87/1.03  --bmc1_min_bound                        0
% 3.87/1.03  --bmc1_max_bound                        -1
% 3.87/1.03  --bmc1_max_bound_default                -1
% 3.87/1.03  --bmc1_symbol_reachability              true
% 3.87/1.03  --bmc1_property_lemmas                  false
% 3.87/1.03  --bmc1_k_induction                      false
% 3.87/1.03  --bmc1_non_equiv_states                 false
% 3.87/1.03  --bmc1_deadlock                         false
% 3.87/1.03  --bmc1_ucm                              false
% 3.87/1.03  --bmc1_add_unsat_core                   none
% 3.87/1.03  --bmc1_unsat_core_children              false
% 3.87/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/1.03  --bmc1_out_stat                         full
% 3.87/1.03  --bmc1_ground_init                      false
% 3.87/1.03  --bmc1_pre_inst_next_state              false
% 3.87/1.03  --bmc1_pre_inst_state                   false
% 3.87/1.03  --bmc1_pre_inst_reach_state             false
% 3.87/1.03  --bmc1_out_unsat_core                   false
% 3.87/1.03  --bmc1_aig_witness_out                  false
% 3.87/1.03  --bmc1_verbose                          false
% 3.87/1.03  --bmc1_dump_clauses_tptp                false
% 3.87/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.87/1.03  --bmc1_dump_file                        -
% 3.87/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.87/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.87/1.03  --bmc1_ucm_extend_mode                  1
% 3.87/1.03  --bmc1_ucm_init_mode                    2
% 3.87/1.03  --bmc1_ucm_cone_mode                    none
% 3.87/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.87/1.03  --bmc1_ucm_relax_model                  4
% 3.87/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.87/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/1.03  --bmc1_ucm_layered_model                none
% 3.87/1.03  --bmc1_ucm_max_lemma_size               10
% 3.87/1.03  
% 3.87/1.03  ------ AIG Options
% 3.87/1.03  
% 3.87/1.03  --aig_mode                              false
% 3.87/1.03  
% 3.87/1.03  ------ Instantiation Options
% 3.87/1.03  
% 3.87/1.03  --instantiation_flag                    true
% 3.87/1.03  --inst_sos_flag                         false
% 3.87/1.03  --inst_sos_phase                        true
% 3.87/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/1.03  --inst_lit_sel_side                     num_symb
% 3.87/1.03  --inst_solver_per_active                1400
% 3.87/1.03  --inst_solver_calls_frac                1.
% 3.87/1.03  --inst_passive_queue_type               priority_queues
% 3.87/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/1.03  --inst_passive_queues_freq              [25;2]
% 3.87/1.03  --inst_dismatching                      true
% 3.87/1.03  --inst_eager_unprocessed_to_passive     true
% 3.87/1.03  --inst_prop_sim_given                   true
% 3.87/1.03  --inst_prop_sim_new                     false
% 3.87/1.03  --inst_subs_new                         false
% 3.87/1.03  --inst_eq_res_simp                      false
% 3.87/1.03  --inst_subs_given                       false
% 3.87/1.03  --inst_orphan_elimination               true
% 3.87/1.03  --inst_learning_loop_flag               true
% 3.87/1.03  --inst_learning_start                   3000
% 3.87/1.03  --inst_learning_factor                  2
% 3.87/1.03  --inst_start_prop_sim_after_learn       3
% 3.87/1.03  --inst_sel_renew                        solver
% 3.87/1.03  --inst_lit_activity_flag                true
% 3.87/1.03  --inst_restr_to_given                   false
% 3.87/1.03  --inst_activity_threshold               500
% 3.87/1.03  --inst_out_proof                        true
% 3.87/1.03  
% 3.87/1.03  ------ Resolution Options
% 3.87/1.03  
% 3.87/1.03  --resolution_flag                       true
% 3.87/1.03  --res_lit_sel                           adaptive
% 3.87/1.03  --res_lit_sel_side                      none
% 3.87/1.03  --res_ordering                          kbo
% 3.87/1.03  --res_to_prop_solver                    active
% 3.87/1.03  --res_prop_simpl_new                    false
% 3.87/1.03  --res_prop_simpl_given                  true
% 3.87/1.03  --res_passive_queue_type                priority_queues
% 3.87/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/1.03  --res_passive_queues_freq               [15;5]
% 3.87/1.03  --res_forward_subs                      full
% 3.87/1.03  --res_backward_subs                     full
% 3.87/1.03  --res_forward_subs_resolution           true
% 3.87/1.03  --res_backward_subs_resolution          true
% 3.87/1.03  --res_orphan_elimination                true
% 3.87/1.03  --res_time_limit                        2.
% 3.87/1.03  --res_out_proof                         true
% 3.87/1.03  
% 3.87/1.03  ------ Superposition Options
% 3.87/1.03  
% 3.87/1.03  --superposition_flag                    true
% 3.87/1.03  --sup_passive_queue_type                priority_queues
% 3.87/1.03  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/1.03  --sup_passive_queues_freq               [1;4]
% 3.87/1.03  --demod_completeness_check              fast
% 3.87/1.03  --demod_use_ground                      true
% 3.87/1.03  --sup_to_prop_solver                    passive
% 3.87/1.03  --sup_prop_simpl_new                    true
% 3.87/1.03  --sup_prop_simpl_given                  true
% 3.87/1.03  --sup_fun_splitting                     false
% 3.87/1.03  --sup_smt_interval                      50000
% 3.87/1.03  
% 3.87/1.03  ------ Superposition Simplification Setup
% 3.87/1.03  
% 3.87/1.03  --sup_indices_passive                   []
% 3.87/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.03  --sup_full_bw                           [BwDemod]
% 3.87/1.03  --sup_immed_triv                        [TrivRules]
% 3.87/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.03  --sup_immed_bw_main                     []
% 3.87/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.03  
% 3.87/1.03  ------ Combination Options
% 3.87/1.03  
% 3.87/1.03  --comb_res_mult                         3
% 3.87/1.03  --comb_sup_mult                         2
% 3.87/1.03  --comb_inst_mult                        10
% 3.87/1.03  
% 3.87/1.03  ------ Debug Options
% 3.87/1.03  
% 3.87/1.03  --dbg_backtrace                         false
% 3.87/1.03  --dbg_dump_prop_clauses                 false
% 3.87/1.03  --dbg_dump_prop_clauses_file            -
% 3.87/1.03  --dbg_out_stat                          false
% 3.87/1.03  
% 3.87/1.03  
% 3.87/1.03  
% 3.87/1.03  
% 3.87/1.03  ------ Proving...
% 3.87/1.03  
% 3.87/1.03  
% 3.87/1.03  % SZS status Theorem for theBenchmark.p
% 3.87/1.03  
% 3.87/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/1.03  
% 3.87/1.03  fof(f16,conjecture,(
% 3.87/1.03    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f17,negated_conjecture,(
% 3.87/1.03    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.87/1.03    inference(negated_conjecture,[],[f16])).
% 3.87/1.03  
% 3.87/1.03  fof(f26,plain,(
% 3.87/1.03    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.87/1.03    inference(ennf_transformation,[],[f17])).
% 3.87/1.03  
% 3.87/1.03  fof(f29,plain,(
% 3.87/1.03    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 3.87/1.03    introduced(choice_axiom,[])).
% 3.87/1.03  
% 3.87/1.03  fof(f30,plain,(
% 3.87/1.03    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 3.87/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f29])).
% 3.87/1.03  
% 3.87/1.03  fof(f49,plain,(
% 3.87/1.03    v1_relat_1(sK0)),
% 3.87/1.03    inference(cnf_transformation,[],[f30])).
% 3.87/1.03  
% 3.87/1.03  fof(f1,axiom,(
% 3.87/1.03    v1_xboole_0(k1_xboole_0)),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f31,plain,(
% 3.87/1.03    v1_xboole_0(k1_xboole_0)),
% 3.87/1.03    inference(cnf_transformation,[],[f1])).
% 3.87/1.03  
% 3.87/1.03  fof(f10,axiom,(
% 3.87/1.03    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f18,plain,(
% 3.87/1.03    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.87/1.03    inference(ennf_transformation,[],[f10])).
% 3.87/1.03  
% 3.87/1.03  fof(f42,plain,(
% 3.87/1.03    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.87/1.03    inference(cnf_transformation,[],[f18])).
% 3.87/1.03  
% 3.87/1.03  fof(f11,axiom,(
% 3.87/1.03    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f19,plain,(
% 3.87/1.03    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.87/1.03    inference(ennf_transformation,[],[f11])).
% 3.87/1.03  
% 3.87/1.03  fof(f20,plain,(
% 3.87/1.03    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.87/1.03    inference(flattening,[],[f19])).
% 3.87/1.03  
% 3.87/1.03  fof(f43,plain,(
% 3.87/1.03    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.87/1.03    inference(cnf_transformation,[],[f20])).
% 3.87/1.03  
% 3.87/1.03  fof(f12,axiom,(
% 3.87/1.03    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f21,plain,(
% 3.87/1.03    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.87/1.03    inference(ennf_transformation,[],[f12])).
% 3.87/1.03  
% 3.87/1.03  fof(f44,plain,(
% 3.87/1.03    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.87/1.03    inference(cnf_transformation,[],[f21])).
% 3.87/1.03  
% 3.87/1.03  fof(f9,axiom,(
% 3.87/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f41,plain,(
% 3.87/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.87/1.03    inference(cnf_transformation,[],[f9])).
% 3.87/1.03  
% 3.87/1.03  fof(f4,axiom,(
% 3.87/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f34,plain,(
% 3.87/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.87/1.03    inference(cnf_transformation,[],[f4])).
% 3.87/1.03  
% 3.87/1.03  fof(f5,axiom,(
% 3.87/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f35,plain,(
% 3.87/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.87/1.03    inference(cnf_transformation,[],[f5])).
% 3.87/1.03  
% 3.87/1.03  fof(f6,axiom,(
% 3.87/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f36,plain,(
% 3.87/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.87/1.03    inference(cnf_transformation,[],[f6])).
% 3.87/1.03  
% 3.87/1.03  fof(f7,axiom,(
% 3.87/1.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f37,plain,(
% 3.87/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.87/1.03    inference(cnf_transformation,[],[f7])).
% 3.87/1.03  
% 3.87/1.03  fof(f51,plain,(
% 3.87/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.87/1.03    inference(definition_unfolding,[],[f36,f37])).
% 3.87/1.03  
% 3.87/1.03  fof(f52,plain,(
% 3.87/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.87/1.03    inference(definition_unfolding,[],[f35,f51])).
% 3.87/1.03  
% 3.87/1.03  fof(f53,plain,(
% 3.87/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.87/1.03    inference(definition_unfolding,[],[f34,f52])).
% 3.87/1.03  
% 3.87/1.03  fof(f54,plain,(
% 3.87/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.87/1.03    inference(definition_unfolding,[],[f41,f53])).
% 3.87/1.03  
% 3.87/1.03  fof(f56,plain,(
% 3.87/1.03    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 3.87/1.03    inference(definition_unfolding,[],[f44,f54])).
% 3.87/1.03  
% 3.87/1.03  fof(f15,axiom,(
% 3.87/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f47,plain,(
% 3.87/1.03    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.87/1.03    inference(cnf_transformation,[],[f15])).
% 3.87/1.03  
% 3.87/1.03  fof(f14,axiom,(
% 3.87/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f24,plain,(
% 3.87/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.87/1.03    inference(ennf_transformation,[],[f14])).
% 3.87/1.03  
% 3.87/1.03  fof(f25,plain,(
% 3.87/1.03    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.87/1.03    inference(flattening,[],[f24])).
% 3.87/1.03  
% 3.87/1.03  fof(f46,plain,(
% 3.87/1.03    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.87/1.03    inference(cnf_transformation,[],[f25])).
% 3.87/1.03  
% 3.87/1.03  fof(f48,plain,(
% 3.87/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.87/1.03    inference(cnf_transformation,[],[f15])).
% 3.87/1.03  
% 3.87/1.03  fof(f3,axiom,(
% 3.87/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f33,plain,(
% 3.87/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.87/1.03    inference(cnf_transformation,[],[f3])).
% 3.87/1.03  
% 3.87/1.03  fof(f2,axiom,(
% 3.87/1.03    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f32,plain,(
% 3.87/1.03    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.87/1.03    inference(cnf_transformation,[],[f2])).
% 3.87/1.03  
% 3.87/1.03  fof(f55,plain,(
% 3.87/1.03    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 3.87/1.03    inference(definition_unfolding,[],[f32,f54])).
% 3.87/1.03  
% 3.87/1.03  fof(f8,axiom,(
% 3.87/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f27,plain,(
% 3.87/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.87/1.03    inference(nnf_transformation,[],[f8])).
% 3.87/1.03  
% 3.87/1.03  fof(f28,plain,(
% 3.87/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.87/1.03    inference(flattening,[],[f27])).
% 3.87/1.03  
% 3.87/1.03  fof(f40,plain,(
% 3.87/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.87/1.03    inference(cnf_transformation,[],[f28])).
% 3.87/1.03  
% 3.87/1.03  fof(f57,plain,(
% 3.87/1.03    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.87/1.03    inference(equality_resolution,[],[f40])).
% 3.87/1.03  
% 3.87/1.03  fof(f13,axiom,(
% 3.87/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 3.87/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/1.03  
% 3.87/1.03  fof(f22,plain,(
% 3.87/1.03    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.87/1.03    inference(ennf_transformation,[],[f13])).
% 3.87/1.03  
% 3.87/1.03  fof(f23,plain,(
% 3.87/1.03    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.87/1.03    inference(flattening,[],[f22])).
% 3.87/1.03  
% 3.87/1.03  fof(f45,plain,(
% 3.87/1.03    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.87/1.03    inference(cnf_transformation,[],[f23])).
% 3.87/1.03  
% 3.87/1.03  fof(f39,plain,(
% 3.87/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.87/1.03    inference(cnf_transformation,[],[f28])).
% 3.87/1.03  
% 3.87/1.03  fof(f58,plain,(
% 3.87/1.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.87/1.03    inference(equality_resolution,[],[f39])).
% 3.87/1.03  
% 3.87/1.03  fof(f50,plain,(
% 3.87/1.03    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 3.87/1.03    inference(cnf_transformation,[],[f30])).
% 3.87/1.03  
% 3.87/1.03  cnf(c_14,negated_conjecture,
% 3.87/1.03      ( v1_relat_1(sK0) ),
% 3.87/1.03      inference(cnf_transformation,[],[f49]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_259,plain,
% 3.87/1.03      ( v1_relat_1(sK0) = iProver_top ),
% 3.87/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_0,plain,
% 3.87/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 3.87/1.03      inference(cnf_transformation,[],[f31]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_266,plain,
% 3.87/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.87/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_6,plain,
% 3.87/1.03      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.87/1.03      inference(cnf_transformation,[],[f42]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_264,plain,
% 3.87/1.03      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.87/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_752,plain,
% 3.87/1.03      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.87/1.03      inference(superposition,[status(thm)],[c_266,c_264]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_7,plain,
% 3.87/1.03      ( ~ v1_relat_1(X0)
% 3.87/1.03      | ~ v1_relat_1(X1)
% 3.87/1.03      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.87/1.03      inference(cnf_transformation,[],[f43]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_263,plain,
% 3.87/1.03      ( v1_relat_1(X0) != iProver_top
% 3.87/1.03      | v1_relat_1(X1) != iProver_top
% 3.87/1.03      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 3.87/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_8,plain,
% 3.87/1.03      ( ~ v1_relat_1(X0)
% 3.87/1.03      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 3.87/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_262,plain,
% 3.87/1.03      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 3.87/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.87/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_839,plain,
% 3.87/1.03      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 3.87/1.03      | v1_relat_1(X1) != iProver_top
% 3.87/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.87/1.03      inference(superposition,[status(thm)],[c_263,c_262]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_1484,plain,
% 3.87/1.03      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
% 3.87/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.87/1.03      inference(superposition,[status(thm)],[c_752,c_839]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_7933,plain,
% 3.87/1.03      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
% 3.87/1.03      inference(superposition,[status(thm)],[c_259,c_1484]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_12,plain,
% 3.87/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.87/1.03      inference(cnf_transformation,[],[f47]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_10,plain,
% 3.87/1.03      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 3.87/1.03      | ~ v1_relat_1(X1)
% 3.87/1.03      | ~ v1_relat_1(X0)
% 3.87/1.03      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 3.87/1.03      inference(cnf_transformation,[],[f46]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_260,plain,
% 3.87/1.03      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 3.87/1.03      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 3.87/1.03      | v1_relat_1(X0) != iProver_top
% 3.87/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.87/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_405,plain,
% 3.87/1.03      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 3.87/1.03      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 3.87/1.03      | v1_relat_1(X0) != iProver_top
% 3.87/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.87/1.03      inference(superposition,[status(thm)],[c_12,c_260]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_11,plain,
% 3.87/1.03      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.87/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_419,plain,
% 3.87/1.03      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.87/1.03      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 3.87/1.03      | v1_relat_1(X0) != iProver_top
% 3.87/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.87/1.03      inference(light_normalisation,[status(thm)],[c_405,c_11]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_28,plain,
% 3.87/1.03      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.87/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_30,plain,
% 3.87/1.03      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.87/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.87/1.03      inference(instantiation,[status(thm)],[c_28]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_37,plain,
% 3.87/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.87/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_853,plain,
% 3.87/1.03      ( v1_relat_1(X0) != iProver_top
% 3.87/1.03      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 3.87/1.03      | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.87/1.03      inference(global_propositional_subsumption,
% 3.87/1.03                [status(thm)],
% 3.87/1.03                [c_419,c_30,c_37]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_854,plain,
% 3.87/1.03      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.87/1.03      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 3.87/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.87/1.03      inference(renaming,[status(thm)],[c_853]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_2,plain,
% 3.87/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 3.87/1.03      inference(cnf_transformation,[],[f33]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_265,plain,
% 3.87/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_860,plain,
% 3.87/1.03      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.87/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.87/1.03      inference(forward_subsumption_resolution,
% 3.87/1.03                [status(thm)],
% 3.87/1.03                [c_854,c_265]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_865,plain,
% 3.87/1.03      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 3.87/1.03      inference(superposition,[status(thm)],[c_259,c_860]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_7940,plain,
% 3.87/1.03      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 3.87/1.03      inference(light_normalisation,[status(thm)],[c_7933,c_865]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_1,plain,
% 3.87/1.03      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.87/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_3,plain,
% 3.87/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.87/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_7941,plain,
% 3.87/1.03      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.87/1.03      inference(demodulation,[status(thm)],[c_7940,c_1,c_3]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_1483,plain,
% 3.87/1.03      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0))))) = k5_relat_1(X0,sK0)
% 3.87/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.87/1.03      inference(superposition,[status(thm)],[c_259,c_839]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_7533,plain,
% 3.87/1.03      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 3.87/1.03      inference(superposition,[status(thm)],[c_752,c_1483]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_9,plain,
% 3.87/1.03      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.87/1.03      | ~ v1_relat_1(X1)
% 3.87/1.03      | ~ v1_relat_1(X0)
% 3.87/1.03      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 3.87/1.03      inference(cnf_transformation,[],[f45]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_261,plain,
% 3.87/1.03      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 3.87/1.03      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.87/1.03      | v1_relat_1(X1) != iProver_top
% 3.87/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.87/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_652,plain,
% 3.87/1.03      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 3.87/1.03      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.87/1.03      | v1_relat_1(X0) != iProver_top
% 3.87/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.87/1.03      inference(superposition,[status(thm)],[c_11,c_261]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_666,plain,
% 3.87/1.03      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.87/1.03      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.87/1.03      | v1_relat_1(X0) != iProver_top
% 3.87/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.87/1.03      inference(light_normalisation,[status(thm)],[c_652,c_12]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_954,plain,
% 3.87/1.03      ( v1_relat_1(X0) != iProver_top
% 3.87/1.03      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.87/1.03      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.87/1.03      inference(global_propositional_subsumption,
% 3.87/1.03                [status(thm)],
% 3.87/1.03                [c_666,c_30,c_37]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_955,plain,
% 3.87/1.03      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.87/1.03      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.87/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.87/1.03      inference(renaming,[status(thm)],[c_954]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_961,plain,
% 3.87/1.03      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.87/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.87/1.03      inference(forward_subsumption_resolution,
% 3.87/1.03                [status(thm)],
% 3.87/1.03                [c_955,c_265]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_966,plain,
% 3.87/1.03      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 3.87/1.03      inference(superposition,[status(thm)],[c_259,c_961]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_7535,plain,
% 3.87/1.03      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 3.87/1.03      inference(light_normalisation,[status(thm)],[c_7533,c_966]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_4,plain,
% 3.87/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.87/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_7536,plain,
% 3.87/1.03      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 3.87/1.03      inference(demodulation,[status(thm)],[c_7535,c_1,c_4]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_13,negated_conjecture,
% 3.87/1.03      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 3.87/1.03      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 3.87/1.03      inference(cnf_transformation,[],[f50]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_7642,plain,
% 3.87/1.03      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 3.87/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 3.87/1.03      inference(demodulation,[status(thm)],[c_7536,c_13]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(c_7643,plain,
% 3.87/1.03      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 3.87/1.03      inference(equality_resolution_simp,[status(thm)],[c_7642]) ).
% 3.87/1.03  
% 3.87/1.03  cnf(contradiction,plain,
% 3.87/1.03      ( $false ),
% 3.87/1.03      inference(minisat,[status(thm)],[c_7941,c_7643]) ).
% 3.87/1.03  
% 3.87/1.03  
% 3.87/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/1.03  
% 3.87/1.03  ------                               Statistics
% 3.87/1.03  
% 3.87/1.03  ------ Selected
% 3.87/1.03  
% 3.87/1.03  total_time:                             0.262
% 3.87/1.03  
%------------------------------------------------------------------------------
