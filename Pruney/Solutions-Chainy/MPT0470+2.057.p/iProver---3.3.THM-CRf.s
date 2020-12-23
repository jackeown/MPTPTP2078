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
% DateTime   : Thu Dec  3 11:44:05 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 451 expanded)
%              Number of clauses        :   69 ( 195 expanded)
%              Number of leaves         :   14 (  84 expanded)
%              Depth                    :   24
%              Number of atoms          :  264 (1082 expanded)
%              Number of equality atoms :  147 ( 509 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f35])).

fof(f56,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f57,plain,
    ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_599,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_592,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_919,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_599,c_592])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_587,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_591,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_590,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_595,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1356,plain,
    ( k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_590,c_595])).

cnf(c_2524,plain,
    ( k4_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1)))) = k1_xboole_0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_591,c_1356])).

cnf(c_6576,plain,
    ( k4_xboole_0(k5_relat_1(X0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK2)),k2_relat_1(k5_relat_1(X0,sK2)))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_2524])).

cnf(c_7612,plain,
    ( k4_xboole_0(k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK2)),k2_relat_1(k5_relat_1(k1_xboole_0,sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_919,c_6576])).

cnf(c_15,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_589,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1475,plain,
    ( k4_xboole_0(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_595])).

cnf(c_3990,plain,
    ( k4_xboole_0(k1_relat_1(k5_relat_1(X0,sK2)),k1_relat_1(X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_1475])).

cnf(c_4020,plain,
    ( k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK2)),k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_919,c_3990])).

cnf(c_18,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4029,plain,
    ( k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK2)),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4020,c_18])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_597,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1355,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_590])).

cnf(c_1363,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1355,c_18])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1364,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1363,c_10])).

cnf(c_34,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_36,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_55,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1376,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1364,c_36,c_55])).

cnf(c_1381,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1376,c_595])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_594,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1468,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_594])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_598,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1933,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_598])).

cnf(c_1943,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_597,c_1933])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_593,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2032,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1943,c_593])).

cnf(c_4113,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4029,c_2032])).

cnf(c_7621,plain,
    ( k4_xboole_0(k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK2)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7612,c_4113])).

cnf(c_7622,plain,
    ( k5_relat_1(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7621,c_10,c_2032])).

cnf(c_16,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_588,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_963,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_588])).

cnf(c_2290,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_963,c_36,c_55])).

cnf(c_2291,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2290])).

cnf(c_2296,plain,
    ( k4_xboole_0(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2291,c_595])).

cnf(c_2297,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2296,c_2032])).

cnf(c_2629,plain,
    ( k2_relat_1(k5_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_587,c_2297])).

cnf(c_2751,plain,
    ( r1_tarski(k5_relat_1(sK2,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK2,k1_xboole_0)),k1_xboole_0)) = iProver_top
    | v1_relat_1(k5_relat_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2629,c_590])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2767,plain,
    ( r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k5_relat_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2751,c_9])).

cnf(c_2865,plain,
    ( k4_xboole_0(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k5_relat_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2767,c_595])).

cnf(c_2866,plain,
    ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k5_relat_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2865,c_2032])).

cnf(c_3013,plain,
    ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_591,c_2866])).

cnf(c_21,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3293,plain,
    ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3013,c_21,c_36,c_55])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3300,plain,
    ( k5_relat_1(k1_xboole_0,sK2) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3293,c_19])).

cnf(c_3301,plain,
    ( k5_relat_1(k1_xboole_0,sK2) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3300])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7622,c_3301])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.36/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/0.99  
% 3.36/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/0.99  
% 3.36/0.99  ------  iProver source info
% 3.36/0.99  
% 3.36/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.36/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/0.99  git: non_committed_changes: false
% 3.36/0.99  git: last_make_outside_of_git: false
% 3.36/0.99  
% 3.36/0.99  ------ 
% 3.36/0.99  ------ Parsing...
% 3.36/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/0.99  
% 3.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.36/0.99  
% 3.36/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/0.99  
% 3.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/0.99  ------ Proving...
% 3.36/0.99  ------ Problem Properties 
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  clauses                                 21
% 3.36/0.99  conjectures                             2
% 3.36/0.99  EPR                                     5
% 3.36/0.99  Horn                                    17
% 3.36/0.99  unary                                   6
% 3.36/0.99  binary                                  10
% 3.36/0.99  lits                                    41
% 3.36/0.99  lits eq                                 12
% 3.36/0.99  fd_pure                                 0
% 3.36/0.99  fd_pseudo                               0
% 3.36/0.99  fd_cond                                 1
% 3.36/0.99  fd_pseudo_cond                          0
% 3.36/0.99  AC symbols                              0
% 3.36/0.99  
% 3.36/0.99  ------ Input Options Time Limit: Unbounded
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  ------ 
% 3.36/0.99  Current options:
% 3.36/0.99  ------ 
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  ------ Proving...
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  % SZS status Theorem for theBenchmark.p
% 3.36/0.99  
% 3.36/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/0.99  
% 3.36/0.99  fof(f2,axiom,(
% 3.36/0.99    v1_xboole_0(k1_xboole_0)),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f39,plain,(
% 3.36/0.99    v1_xboole_0(k1_xboole_0)),
% 3.36/0.99    inference(cnf_transformation,[],[f2])).
% 3.36/0.99  
% 3.36/0.99  fof(f7,axiom,(
% 3.36/0.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f19,plain,(
% 3.36/0.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.36/0.99    inference(ennf_transformation,[],[f7])).
% 3.36/0.99  
% 3.36/0.99  fof(f49,plain,(
% 3.36/0.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f19])).
% 3.36/0.99  
% 3.36/0.99  fof(f13,conjecture,(
% 3.36/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f14,negated_conjecture,(
% 3.36/0.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.36/0.99    inference(negated_conjecture,[],[f13])).
% 3.36/0.99  
% 3.36/0.99  fof(f25,plain,(
% 3.36/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.36/0.99    inference(ennf_transformation,[],[f14])).
% 3.36/0.99  
% 3.36/0.99  fof(f35,plain,(
% 3.36/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)) & v1_relat_1(sK2))),
% 3.36/0.99    introduced(choice_axiom,[])).
% 3.36/0.99  
% 3.36/0.99  fof(f36,plain,(
% 3.36/0.99    (k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)) & v1_relat_1(sK2)),
% 3.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f35])).
% 3.36/0.99  
% 3.36/0.99  fof(f56,plain,(
% 3.36/0.99    v1_relat_1(sK2)),
% 3.36/0.99    inference(cnf_transformation,[],[f36])).
% 3.36/0.99  
% 3.36/0.99  fof(f8,axiom,(
% 3.36/0.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f20,plain,(
% 3.36/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.36/0.99    inference(ennf_transformation,[],[f8])).
% 3.36/0.99  
% 3.36/0.99  fof(f21,plain,(
% 3.36/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(flattening,[],[f20])).
% 3.36/0.99  
% 3.36/0.99  fof(f50,plain,(
% 3.36/0.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f21])).
% 3.36/0.99  
% 3.36/0.99  fof(f9,axiom,(
% 3.36/0.99    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f22,plain,(
% 3.36/0.99    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(ennf_transformation,[],[f9])).
% 3.36/0.99  
% 3.36/0.99  fof(f51,plain,(
% 3.36/0.99    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f22])).
% 3.36/0.99  
% 3.36/0.99  fof(f4,axiom,(
% 3.36/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f16,plain,(
% 3.36/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 3.36/0.99    inference(unused_predicate_definition_removal,[],[f4])).
% 3.36/0.99  
% 3.36/0.99  fof(f18,plain,(
% 3.36/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 3.36/0.99    inference(ennf_transformation,[],[f16])).
% 3.36/0.99  
% 3.36/0.99  fof(f43,plain,(
% 3.36/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f18])).
% 3.36/0.99  
% 3.36/0.99  fof(f10,axiom,(
% 3.36/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f23,plain,(
% 3.36/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(ennf_transformation,[],[f10])).
% 3.36/0.99  
% 3.36/0.99  fof(f52,plain,(
% 3.36/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f23])).
% 3.36/0.99  
% 3.36/0.99  fof(f12,axiom,(
% 3.36/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f54,plain,(
% 3.36/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.36/0.99    inference(cnf_transformation,[],[f12])).
% 3.36/0.99  
% 3.36/0.99  fof(f3,axiom,(
% 3.36/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f15,plain,(
% 3.36/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.36/0.99    inference(rectify,[],[f3])).
% 3.36/0.99  
% 3.36/0.99  fof(f17,plain,(
% 3.36/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.36/0.99    inference(ennf_transformation,[],[f15])).
% 3.36/0.99  
% 3.36/0.99  fof(f30,plain,(
% 3.36/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.36/0.99    introduced(choice_axiom,[])).
% 3.36/0.99  
% 3.36/0.99  fof(f31,plain,(
% 3.36/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f30])).
% 3.36/0.99  
% 3.36/0.99  fof(f41,plain,(
% 3.36/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f31])).
% 3.36/0.99  
% 3.36/0.99  fof(f55,plain,(
% 3.36/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.36/0.99    inference(cnf_transformation,[],[f12])).
% 3.36/0.99  
% 3.36/0.99  fof(f6,axiom,(
% 3.36/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f33,plain,(
% 3.36/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.36/0.99    inference(nnf_transformation,[],[f6])).
% 3.36/0.99  
% 3.36/0.99  fof(f34,plain,(
% 3.36/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.36/0.99    inference(flattening,[],[f33])).
% 3.36/0.99  
% 3.36/0.99  fof(f47,plain,(
% 3.36/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.36/0.99    inference(cnf_transformation,[],[f34])).
% 3.36/0.99  
% 3.36/0.99  fof(f59,plain,(
% 3.36/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.36/0.99    inference(equality_resolution,[],[f47])).
% 3.36/0.99  
% 3.36/0.99  fof(f5,axiom,(
% 3.36/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f32,plain,(
% 3.36/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.36/0.99    inference(nnf_transformation,[],[f5])).
% 3.36/0.99  
% 3.36/0.99  fof(f45,plain,(
% 3.36/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.36/0.99    inference(cnf_transformation,[],[f32])).
% 3.36/0.99  
% 3.36/0.99  fof(f42,plain,(
% 3.36/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f31])).
% 3.36/0.99  
% 3.36/0.99  fof(f44,plain,(
% 3.36/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f32])).
% 3.36/0.99  
% 3.36/0.99  fof(f11,axiom,(
% 3.36/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f24,plain,(
% 3.36/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(ennf_transformation,[],[f11])).
% 3.36/0.99  
% 3.36/0.99  fof(f53,plain,(
% 3.36/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f24])).
% 3.36/0.99  
% 3.36/0.99  fof(f48,plain,(
% 3.36/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.36/0.99    inference(cnf_transformation,[],[f34])).
% 3.36/0.99  
% 3.36/0.99  fof(f58,plain,(
% 3.36/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.36/0.99    inference(equality_resolution,[],[f48])).
% 3.36/0.99  
% 3.36/0.99  fof(f57,plain,(
% 3.36/0.99    k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)),
% 3.36/0.99    inference(cnf_transformation,[],[f36])).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2,plain,
% 3.36/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.36/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_599,plain,
% 3.36/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_12,plain,
% 3.36/0.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.36/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_592,plain,
% 3.36/0.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_919,plain,
% 3.36/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_599,c_592]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_20,negated_conjecture,
% 3.36/0.99      ( v1_relat_1(sK2) ),
% 3.36/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_587,plain,
% 3.36/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_13,plain,
% 3.36/0.99      ( ~ v1_relat_1(X0)
% 3.36/0.99      | ~ v1_relat_1(X1)
% 3.36/0.99      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.36/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_591,plain,
% 3.36/0.99      ( v1_relat_1(X0) != iProver_top
% 3.36/0.99      | v1_relat_1(X1) != iProver_top
% 3.36/0.99      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_14,plain,
% 3.36/0.99      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 3.36/0.99      | ~ v1_relat_1(X0) ),
% 3.36/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_590,plain,
% 3.36/0.99      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_6,plain,
% 3.36/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.36/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_595,plain,
% 3.36/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.36/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1356,plain,
% 3.36/0.99      ( k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_590,c_595]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2524,plain,
% 3.36/0.99      ( k4_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1)))) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(X1) != iProver_top
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_591,c_1356]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_6576,plain,
% 3.36/0.99      ( k4_xboole_0(k5_relat_1(X0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK2)),k2_relat_1(k5_relat_1(X0,sK2)))) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_587,c_2524]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_7612,plain,
% 3.36/0.99      ( k4_xboole_0(k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK2)),k2_relat_1(k5_relat_1(k1_xboole_0,sK2)))) = k1_xboole_0 ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_919,c_6576]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_15,plain,
% 3.36/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.36/0.99      | ~ v1_relat_1(X1)
% 3.36/0.99      | ~ v1_relat_1(X0) ),
% 3.36/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_589,plain,
% 3.36/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.36/0.99      | v1_relat_1(X1) != iProver_top
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1475,plain,
% 3.36/0.99      ( k4_xboole_0(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(X0) != iProver_top
% 3.36/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_589,c_595]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_3990,plain,
% 3.36/0.99      ( k4_xboole_0(k1_relat_1(k5_relat_1(X0,sK2)),k1_relat_1(X0)) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_587,c_1475]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4020,plain,
% 3.36/0.99      ( k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK2)),k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_919,c_3990]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_18,plain,
% 3.36/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.36/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4029,plain,
% 3.36/0.99      ( k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK2)),k1_xboole_0) = k1_xboole_0 ),
% 3.36/0.99      inference(light_normalisation,[status(thm)],[c_4020,c_18]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4,plain,
% 3.36/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 3.36/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_597,plain,
% 3.36/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.36/0.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_17,plain,
% 3.36/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.36/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1355,plain,
% 3.36/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
% 3.36/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_17,c_590]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1363,plain,
% 3.36/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 3.36/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(light_normalisation,[status(thm)],[c_1355,c_18]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_10,plain,
% 3.36/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.36/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1364,plain,
% 3.36/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
% 3.36/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(demodulation,[status(thm)],[c_1363,c_10]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_34,plain,
% 3.36/0.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_36,plain,
% 3.36/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.36/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_34]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_55,plain,
% 3.36/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1376,plain,
% 3.36/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.36/0.99      inference(global_propositional_subsumption,
% 3.36/0.99                [status(thm)],
% 3.36/0.99                [c_1364,c_36,c_55]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1381,plain,
% 3.36/0.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_1376,c_595]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_7,plain,
% 3.36/0.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.36/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_594,plain,
% 3.36/0.99      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1468,plain,
% 3.36/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_1381,c_594]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_3,plain,
% 3.36/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 3.36/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_598,plain,
% 3.36/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.36/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.36/0.99      | r2_hidden(X2,X1) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1933,plain,
% 3.36/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_1468,c_598]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1943,plain,
% 3.36/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_597,c_1933]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_8,plain,
% 3.36/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.36/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_593,plain,
% 3.36/0.99      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2032,plain,
% 3.36/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_1943,c_593]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4113,plain,
% 3.36/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK2)) = k1_xboole_0 ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_4029,c_2032]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_7621,plain,
% 3.36/0.99      ( k4_xboole_0(k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK2)))) = k1_xboole_0 ),
% 3.36/0.99      inference(light_normalisation,[status(thm)],[c_7612,c_4113]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_7622,plain,
% 3.36/0.99      ( k5_relat_1(k1_xboole_0,sK2) = k1_xboole_0 ),
% 3.36/0.99      inference(demodulation,[status(thm)],[c_7621,c_10,c_2032]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_16,plain,
% 3.36/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.36/0.99      | ~ v1_relat_1(X1)
% 3.36/0.99      | ~ v1_relat_1(X0) ),
% 3.36/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_588,plain,
% 3.36/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.36/0.99      | v1_relat_1(X1) != iProver_top
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_963,plain,
% 3.36/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 3.36/0.99      | v1_relat_1(X0) != iProver_top
% 3.36/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_17,c_588]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2290,plain,
% 3.36/0.99      ( v1_relat_1(X0) != iProver_top
% 3.36/0.99      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 3.36/0.99      inference(global_propositional_subsumption,
% 3.36/0.99                [status(thm)],
% 3.36/0.99                [c_963,c_36,c_55]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2291,plain,
% 3.36/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(renaming,[status(thm)],[c_2290]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2296,plain,
% 3.36/0.99      ( k4_xboole_0(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_2291,c_595]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2297,plain,
% 3.36/0.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(demodulation,[status(thm)],[c_2296,c_2032]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2629,plain,
% 3.36/0.99      ( k2_relat_1(k5_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_587,c_2297]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2751,plain,
% 3.36/0.99      ( r1_tarski(k5_relat_1(sK2,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK2,k1_xboole_0)),k1_xboole_0)) = iProver_top
% 3.36/0.99      | v1_relat_1(k5_relat_1(sK2,k1_xboole_0)) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_2629,c_590]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_9,plain,
% 3.36/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.36/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2767,plain,
% 3.36/0.99      ( r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0) = iProver_top
% 3.36/0.99      | v1_relat_1(k5_relat_1(sK2,k1_xboole_0)) != iProver_top ),
% 3.36/0.99      inference(demodulation,[status(thm)],[c_2751,c_9]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2865,plain,
% 3.36/0.99      ( k4_xboole_0(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(k5_relat_1(sK2,k1_xboole_0)) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_2767,c_595]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2866,plain,
% 3.36/0.99      ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(k5_relat_1(sK2,k1_xboole_0)) != iProver_top ),
% 3.36/0.99      inference(demodulation,[status(thm)],[c_2865,c_2032]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_3013,plain,
% 3.36/0.99      ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(sK2) != iProver_top
% 3.36/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_591,c_2866]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_21,plain,
% 3.36/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_3293,plain,
% 3.36/0.99      ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 3.36/0.99      inference(global_propositional_subsumption,
% 3.36/0.99                [status(thm)],
% 3.36/0.99                [c_3013,c_21,c_36,c_55]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_19,negated_conjecture,
% 3.36/0.99      ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
% 3.36/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
% 3.36/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_3300,plain,
% 3.36/0.99      ( k5_relat_1(k1_xboole_0,sK2) != k1_xboole_0
% 3.36/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.36/0.99      inference(demodulation,[status(thm)],[c_3293,c_19]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_3301,plain,
% 3.36/0.99      ( k5_relat_1(k1_xboole_0,sK2) != k1_xboole_0 ),
% 3.36/0.99      inference(equality_resolution_simp,[status(thm)],[c_3300]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(contradiction,plain,
% 3.36/0.99      ( $false ),
% 3.36/0.99      inference(minisat,[status(thm)],[c_7622,c_3301]) ).
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/0.99  
% 3.36/0.99  ------                               Statistics
% 3.36/0.99  
% 3.36/0.99  ------ Selected
% 3.36/0.99  
% 3.36/0.99  total_time:                             0.243
% 3.36/0.99  
%------------------------------------------------------------------------------
