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
% DateTime   : Thu Dec  3 11:44:42 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 377 expanded)
%              Number of clauses        :   52 ( 130 expanded)
%              Number of leaves         :   11 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          :  220 (1135 expanded)
%              Number of equality atoms :  105 ( 413 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k7_relat_1(sK2,sK1)) != sK1
      & r1_tarski(sK1,k1_relat_1(sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != sK1
    & r1_tarski(sK1,k1_relat_1(sK2))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f22])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f38,plain,(
    r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    k1_relat_1(k7_relat_1(sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_319,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_320,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_685,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_319,c_320])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_324,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_325,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4608,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_324,c_325])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_322,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7214,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
    | r2_hidden(sK0(X0,X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4608,c_322])).

cnf(c_11869,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X1,X1)
    | r2_hidden(sK0(X1,X1,X0),k4_xboole_0(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_7214])).

cnf(c_11948,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r2_hidden(sK0(X0,X0,X1),k4_xboole_0(X1,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11869,c_6])).

cnf(c_12305,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0
    | r2_hidden(sK0(X0,X0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_685,c_11948])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5209,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_685,c_10])).

cnf(c_9,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_505,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_10,c_10])).

cnf(c_791,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_9,c_505])).

cnf(c_5589,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5209,c_791])).

cnf(c_793,plain,
    ( k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1)))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_505,c_10])).

cnf(c_6511,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5589,c_793])).

cnf(c_5575,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_5209])).

cnf(c_6549,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6511,c_5575])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_321,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7213,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
    | r2_hidden(sK0(X0,X0,k4_xboole_0(X1,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4608,c_321])).

cnf(c_10602,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X1,X1)
    | r2_hidden(sK0(X1,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6549,c_7213])).

cnf(c_10683,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0
    | r2_hidden(sK0(X0,X0,k1_xboole_0),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10602,c_6549])).

cnf(c_11871,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X1)
    | r2_hidden(sK0(X0,X0,k1_xboole_0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_685,c_7214])).

cnf(c_11940,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0
    | r2_hidden(sK0(X0,X0,k1_xboole_0),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11871,c_685])).

cnf(c_12316,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12305,c_10683,c_11940])).

cnf(c_12328,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_12316,c_6])).

cnf(c_12365,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(instantiation,[status(thm)],[c_12328])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_316,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_318,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_353,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_318,c_10])).

cnf(c_786,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_316,c_353])).

cnf(c_1559,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_786])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_317,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_686,plain,
    ( k4_xboole_0(sK1,k1_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_317,c_320])).

cnf(c_1097,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_relat_1(sK2))) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_686,c_10])).

cnf(c_1611,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1559,c_1097])).

cnf(c_12,negated_conjecture,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5985,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != sK1 ),
    inference(demodulation,[status(thm)],[c_1611,c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12365,c_5985])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:59:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.59/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/1.52  
% 7.59/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.59/1.52  
% 7.59/1.52  ------  iProver source info
% 7.59/1.52  
% 7.59/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.59/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.59/1.52  git: non_committed_changes: false
% 7.59/1.52  git: last_make_outside_of_git: false
% 7.59/1.52  
% 7.59/1.52  ------ 
% 7.59/1.52  
% 7.59/1.52  ------ Input Options
% 7.59/1.52  
% 7.59/1.52  --out_options                           all
% 7.59/1.52  --tptp_safe_out                         true
% 7.59/1.52  --problem_path                          ""
% 7.59/1.52  --include_path                          ""
% 7.59/1.52  --clausifier                            res/vclausify_rel
% 7.59/1.52  --clausifier_options                    --mode clausify
% 7.59/1.52  --stdin                                 false
% 7.59/1.52  --stats_out                             sel
% 7.59/1.52  
% 7.59/1.52  ------ General Options
% 7.59/1.52  
% 7.59/1.52  --fof                                   false
% 7.59/1.52  --time_out_real                         604.99
% 7.59/1.52  --time_out_virtual                      -1.
% 7.59/1.52  --symbol_type_check                     false
% 7.59/1.52  --clausify_out                          false
% 7.59/1.52  --sig_cnt_out                           false
% 7.59/1.52  --trig_cnt_out                          false
% 7.59/1.52  --trig_cnt_out_tolerance                1.
% 7.59/1.52  --trig_cnt_out_sk_spl                   false
% 7.59/1.52  --abstr_cl_out                          false
% 7.59/1.52  
% 7.59/1.52  ------ Global Options
% 7.59/1.52  
% 7.59/1.52  --schedule                              none
% 7.59/1.52  --add_important_lit                     false
% 7.59/1.52  --prop_solver_per_cl                    1000
% 7.59/1.52  --min_unsat_core                        false
% 7.59/1.52  --soft_assumptions                      false
% 7.59/1.52  --soft_lemma_size                       3
% 7.59/1.52  --prop_impl_unit_size                   0
% 7.59/1.52  --prop_impl_unit                        []
% 7.59/1.52  --share_sel_clauses                     true
% 7.59/1.52  --reset_solvers                         false
% 7.59/1.52  --bc_imp_inh                            [conj_cone]
% 7.59/1.52  --conj_cone_tolerance                   3.
% 7.59/1.52  --extra_neg_conj                        none
% 7.59/1.52  --large_theory_mode                     true
% 7.59/1.52  --prolific_symb_bound                   200
% 7.59/1.52  --lt_threshold                          2000
% 7.59/1.52  --clause_weak_htbl                      true
% 7.59/1.52  --gc_record_bc_elim                     false
% 7.59/1.52  
% 7.59/1.52  ------ Preprocessing Options
% 7.59/1.52  
% 7.59/1.52  --preprocessing_flag                    true
% 7.59/1.52  --time_out_prep_mult                    0.1
% 7.59/1.52  --splitting_mode                        input
% 7.59/1.52  --splitting_grd                         true
% 7.59/1.52  --splitting_cvd                         false
% 7.59/1.52  --splitting_cvd_svl                     false
% 7.59/1.52  --splitting_nvd                         32
% 7.59/1.52  --sub_typing                            true
% 7.59/1.52  --prep_gs_sim                           false
% 7.59/1.52  --prep_unflatten                        true
% 7.59/1.52  --prep_res_sim                          true
% 7.59/1.52  --prep_upred                            true
% 7.59/1.52  --prep_sem_filter                       exhaustive
% 7.59/1.52  --prep_sem_filter_out                   false
% 7.59/1.52  --pred_elim                             false
% 7.59/1.52  --res_sim_input                         true
% 7.59/1.52  --eq_ax_congr_red                       true
% 7.59/1.52  --pure_diseq_elim                       true
% 7.59/1.52  --brand_transform                       false
% 7.59/1.52  --non_eq_to_eq                          false
% 7.59/1.52  --prep_def_merge                        true
% 7.59/1.52  --prep_def_merge_prop_impl              false
% 7.59/1.52  --prep_def_merge_mbd                    true
% 7.59/1.52  --prep_def_merge_tr_red                 false
% 7.59/1.52  --prep_def_merge_tr_cl                  false
% 7.59/1.52  --smt_preprocessing                     true
% 7.59/1.52  --smt_ac_axioms                         fast
% 7.59/1.52  --preprocessed_out                      false
% 7.59/1.52  --preprocessed_stats                    false
% 7.59/1.52  
% 7.59/1.52  ------ Abstraction refinement Options
% 7.59/1.52  
% 7.59/1.52  --abstr_ref                             []
% 7.59/1.52  --abstr_ref_prep                        false
% 7.59/1.52  --abstr_ref_until_sat                   false
% 7.59/1.52  --abstr_ref_sig_restrict                funpre
% 7.59/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.52  --abstr_ref_under                       []
% 7.59/1.52  
% 7.59/1.52  ------ SAT Options
% 7.59/1.52  
% 7.59/1.52  --sat_mode                              false
% 7.59/1.52  --sat_fm_restart_options                ""
% 7.59/1.52  --sat_gr_def                            false
% 7.59/1.52  --sat_epr_types                         true
% 7.59/1.52  --sat_non_cyclic_types                  false
% 7.59/1.52  --sat_finite_models                     false
% 7.59/1.52  --sat_fm_lemmas                         false
% 7.59/1.52  --sat_fm_prep                           false
% 7.59/1.52  --sat_fm_uc_incr                        true
% 7.59/1.52  --sat_out_model                         small
% 7.59/1.52  --sat_out_clauses                       false
% 7.59/1.52  
% 7.59/1.52  ------ QBF Options
% 7.59/1.52  
% 7.59/1.52  --qbf_mode                              false
% 7.59/1.52  --qbf_elim_univ                         false
% 7.59/1.52  --qbf_dom_inst                          none
% 7.59/1.52  --qbf_dom_pre_inst                      false
% 7.59/1.52  --qbf_sk_in                             false
% 7.59/1.52  --qbf_pred_elim                         true
% 7.59/1.52  --qbf_split                             512
% 7.59/1.52  
% 7.59/1.52  ------ BMC1 Options
% 7.59/1.52  
% 7.59/1.52  --bmc1_incremental                      false
% 7.59/1.52  --bmc1_axioms                           reachable_all
% 7.59/1.52  --bmc1_min_bound                        0
% 7.59/1.52  --bmc1_max_bound                        -1
% 7.59/1.52  --bmc1_max_bound_default                -1
% 7.59/1.52  --bmc1_symbol_reachability              true
% 7.59/1.52  --bmc1_property_lemmas                  false
% 7.59/1.52  --bmc1_k_induction                      false
% 7.59/1.52  --bmc1_non_equiv_states                 false
% 7.59/1.52  --bmc1_deadlock                         false
% 7.59/1.52  --bmc1_ucm                              false
% 7.59/1.52  --bmc1_add_unsat_core                   none
% 7.59/1.52  --bmc1_unsat_core_children              false
% 7.59/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.52  --bmc1_out_stat                         full
% 7.59/1.52  --bmc1_ground_init                      false
% 7.59/1.52  --bmc1_pre_inst_next_state              false
% 7.59/1.52  --bmc1_pre_inst_state                   false
% 7.59/1.52  --bmc1_pre_inst_reach_state             false
% 7.59/1.52  --bmc1_out_unsat_core                   false
% 7.59/1.52  --bmc1_aig_witness_out                  false
% 7.59/1.52  --bmc1_verbose                          false
% 7.59/1.52  --bmc1_dump_clauses_tptp                false
% 7.59/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.52  --bmc1_dump_file                        -
% 7.59/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.52  --bmc1_ucm_extend_mode                  1
% 7.59/1.52  --bmc1_ucm_init_mode                    2
% 7.59/1.52  --bmc1_ucm_cone_mode                    none
% 7.59/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.52  --bmc1_ucm_relax_model                  4
% 7.59/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.52  --bmc1_ucm_layered_model                none
% 7.59/1.52  --bmc1_ucm_max_lemma_size               10
% 7.59/1.52  
% 7.59/1.52  ------ AIG Options
% 7.59/1.52  
% 7.59/1.52  --aig_mode                              false
% 7.59/1.52  
% 7.59/1.52  ------ Instantiation Options
% 7.59/1.52  
% 7.59/1.52  --instantiation_flag                    true
% 7.59/1.52  --inst_sos_flag                         false
% 7.59/1.52  --inst_sos_phase                        true
% 7.59/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.52  --inst_lit_sel_side                     num_symb
% 7.59/1.52  --inst_solver_per_active                1400
% 7.59/1.52  --inst_solver_calls_frac                1.
% 7.59/1.52  --inst_passive_queue_type               priority_queues
% 7.59/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.52  --inst_passive_queues_freq              [25;2]
% 7.59/1.52  --inst_dismatching                      true
% 7.59/1.52  --inst_eager_unprocessed_to_passive     true
% 7.59/1.52  --inst_prop_sim_given                   true
% 7.59/1.52  --inst_prop_sim_new                     false
% 7.59/1.52  --inst_subs_new                         false
% 7.59/1.52  --inst_eq_res_simp                      false
% 7.59/1.52  --inst_subs_given                       false
% 7.59/1.52  --inst_orphan_elimination               true
% 7.59/1.52  --inst_learning_loop_flag               true
% 7.59/1.52  --inst_learning_start                   3000
% 7.59/1.52  --inst_learning_factor                  2
% 7.59/1.52  --inst_start_prop_sim_after_learn       3
% 7.59/1.52  --inst_sel_renew                        solver
% 7.59/1.52  --inst_lit_activity_flag                true
% 7.59/1.52  --inst_restr_to_given                   false
% 7.59/1.52  --inst_activity_threshold               500
% 7.59/1.52  --inst_out_proof                        true
% 7.59/1.52  
% 7.59/1.52  ------ Resolution Options
% 7.59/1.52  
% 7.59/1.52  --resolution_flag                       true
% 7.59/1.52  --res_lit_sel                           adaptive
% 7.59/1.52  --res_lit_sel_side                      none
% 7.59/1.52  --res_ordering                          kbo
% 7.59/1.52  --res_to_prop_solver                    active
% 7.59/1.52  --res_prop_simpl_new                    false
% 7.59/1.52  --res_prop_simpl_given                  true
% 7.59/1.52  --res_passive_queue_type                priority_queues
% 7.59/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.52  --res_passive_queues_freq               [15;5]
% 7.59/1.52  --res_forward_subs                      full
% 7.59/1.52  --res_backward_subs                     full
% 7.59/1.52  --res_forward_subs_resolution           true
% 7.59/1.52  --res_backward_subs_resolution          true
% 7.59/1.52  --res_orphan_elimination                true
% 7.59/1.52  --res_time_limit                        2.
% 7.59/1.52  --res_out_proof                         true
% 7.59/1.52  
% 7.59/1.52  ------ Superposition Options
% 7.59/1.52  
% 7.59/1.52  --superposition_flag                    true
% 7.59/1.52  --sup_passive_queue_type                priority_queues
% 7.59/1.52  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.52  --sup_passive_queues_freq               [1;4]
% 7.59/1.52  --demod_completeness_check              fast
% 7.59/1.52  --demod_use_ground                      true
% 7.59/1.52  --sup_to_prop_solver                    passive
% 7.59/1.52  --sup_prop_simpl_new                    true
% 7.59/1.52  --sup_prop_simpl_given                  true
% 7.59/1.52  --sup_fun_splitting                     false
% 7.59/1.52  --sup_smt_interval                      50000
% 7.59/1.52  
% 7.59/1.52  ------ Superposition Simplification Setup
% 7.59/1.52  
% 7.59/1.52  --sup_indices_passive                   []
% 7.59/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.52  --sup_full_bw                           [BwDemod]
% 7.59/1.52  --sup_immed_triv                        [TrivRules]
% 7.59/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.52  --sup_immed_bw_main                     []
% 7.59/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.52  
% 7.59/1.52  ------ Combination Options
% 7.59/1.52  
% 7.59/1.52  --comb_res_mult                         3
% 7.59/1.52  --comb_sup_mult                         2
% 7.59/1.52  --comb_inst_mult                        10
% 7.59/1.52  
% 7.59/1.52  ------ Debug Options
% 7.59/1.52  
% 7.59/1.52  --dbg_backtrace                         false
% 7.59/1.52  --dbg_dump_prop_clauses                 false
% 7.59/1.52  --dbg_dump_prop_clauses_file            -
% 7.59/1.52  --dbg_out_stat                          false
% 7.59/1.52  ------ Parsing...
% 7.59/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.52  
% 7.59/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.59/1.52  
% 7.59/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.52  
% 7.59/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.52  ------ Proving...
% 7.59/1.52  ------ Problem Properties 
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  clauses                                 15
% 7.59/1.52  conjectures                             3
% 7.59/1.52  EPR                                     2
% 7.59/1.52  Horn                                    11
% 7.59/1.52  unary                                   7
% 7.59/1.52  binary                                  4
% 7.59/1.52  lits                                    28
% 7.59/1.52  lits eq                                 9
% 7.59/1.52  fd_pure                                 0
% 7.59/1.52  fd_pseudo                               0
% 7.59/1.52  fd_cond                                 0
% 7.59/1.52  fd_pseudo_cond                          3
% 7.59/1.52  AC symbols                              0
% 7.59/1.52  
% 7.59/1.52  ------ Input Options Time Limit: Unbounded
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  ------ 
% 7.59/1.52  Current options:
% 7.59/1.52  ------ 
% 7.59/1.52  
% 7.59/1.52  ------ Input Options
% 7.59/1.52  
% 7.59/1.52  --out_options                           all
% 7.59/1.52  --tptp_safe_out                         true
% 7.59/1.52  --problem_path                          ""
% 7.59/1.52  --include_path                          ""
% 7.59/1.52  --clausifier                            res/vclausify_rel
% 7.59/1.52  --clausifier_options                    --mode clausify
% 7.59/1.52  --stdin                                 false
% 7.59/1.52  --stats_out                             sel
% 7.59/1.52  
% 7.59/1.52  ------ General Options
% 7.59/1.52  
% 7.59/1.52  --fof                                   false
% 7.59/1.52  --time_out_real                         604.99
% 7.59/1.52  --time_out_virtual                      -1.
% 7.59/1.52  --symbol_type_check                     false
% 7.59/1.52  --clausify_out                          false
% 7.59/1.52  --sig_cnt_out                           false
% 7.59/1.52  --trig_cnt_out                          false
% 7.59/1.52  --trig_cnt_out_tolerance                1.
% 7.59/1.52  --trig_cnt_out_sk_spl                   false
% 7.59/1.52  --abstr_cl_out                          false
% 7.59/1.52  
% 7.59/1.52  ------ Global Options
% 7.59/1.52  
% 7.59/1.52  --schedule                              none
% 7.59/1.52  --add_important_lit                     false
% 7.59/1.52  --prop_solver_per_cl                    1000
% 7.59/1.52  --min_unsat_core                        false
% 7.59/1.52  --soft_assumptions                      false
% 7.59/1.52  --soft_lemma_size                       3
% 7.59/1.52  --prop_impl_unit_size                   0
% 7.59/1.52  --prop_impl_unit                        []
% 7.59/1.52  --share_sel_clauses                     true
% 7.59/1.52  --reset_solvers                         false
% 7.59/1.52  --bc_imp_inh                            [conj_cone]
% 7.59/1.52  --conj_cone_tolerance                   3.
% 7.59/1.52  --extra_neg_conj                        none
% 7.59/1.52  --large_theory_mode                     true
% 7.59/1.52  --prolific_symb_bound                   200
% 7.59/1.52  --lt_threshold                          2000
% 7.59/1.52  --clause_weak_htbl                      true
% 7.59/1.52  --gc_record_bc_elim                     false
% 7.59/1.52  
% 7.59/1.52  ------ Preprocessing Options
% 7.59/1.52  
% 7.59/1.52  --preprocessing_flag                    true
% 7.59/1.52  --time_out_prep_mult                    0.1
% 7.59/1.52  --splitting_mode                        input
% 7.59/1.52  --splitting_grd                         true
% 7.59/1.52  --splitting_cvd                         false
% 7.59/1.52  --splitting_cvd_svl                     false
% 7.59/1.52  --splitting_nvd                         32
% 7.59/1.52  --sub_typing                            true
% 7.59/1.52  --prep_gs_sim                           false
% 7.59/1.52  --prep_unflatten                        true
% 7.59/1.52  --prep_res_sim                          true
% 7.59/1.52  --prep_upred                            true
% 7.59/1.52  --prep_sem_filter                       exhaustive
% 7.59/1.52  --prep_sem_filter_out                   false
% 7.59/1.52  --pred_elim                             false
% 7.59/1.52  --res_sim_input                         true
% 7.59/1.52  --eq_ax_congr_red                       true
% 7.59/1.52  --pure_diseq_elim                       true
% 7.59/1.52  --brand_transform                       false
% 7.59/1.52  --non_eq_to_eq                          false
% 7.59/1.52  --prep_def_merge                        true
% 7.59/1.52  --prep_def_merge_prop_impl              false
% 7.59/1.52  --prep_def_merge_mbd                    true
% 7.59/1.52  --prep_def_merge_tr_red                 false
% 7.59/1.52  --prep_def_merge_tr_cl                  false
% 7.59/1.52  --smt_preprocessing                     true
% 7.59/1.52  --smt_ac_axioms                         fast
% 7.59/1.52  --preprocessed_out                      false
% 7.59/1.52  --preprocessed_stats                    false
% 7.59/1.52  
% 7.59/1.52  ------ Abstraction refinement Options
% 7.59/1.52  
% 7.59/1.52  --abstr_ref                             []
% 7.59/1.52  --abstr_ref_prep                        false
% 7.59/1.52  --abstr_ref_until_sat                   false
% 7.59/1.52  --abstr_ref_sig_restrict                funpre
% 7.59/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.52  --abstr_ref_under                       []
% 7.59/1.52  
% 7.59/1.52  ------ SAT Options
% 7.59/1.52  
% 7.59/1.52  --sat_mode                              false
% 7.59/1.52  --sat_fm_restart_options                ""
% 7.59/1.52  --sat_gr_def                            false
% 7.59/1.52  --sat_epr_types                         true
% 7.59/1.52  --sat_non_cyclic_types                  false
% 7.59/1.52  --sat_finite_models                     false
% 7.59/1.52  --sat_fm_lemmas                         false
% 7.59/1.52  --sat_fm_prep                           false
% 7.59/1.52  --sat_fm_uc_incr                        true
% 7.59/1.52  --sat_out_model                         small
% 7.59/1.52  --sat_out_clauses                       false
% 7.59/1.52  
% 7.59/1.52  ------ QBF Options
% 7.59/1.52  
% 7.59/1.52  --qbf_mode                              false
% 7.59/1.52  --qbf_elim_univ                         false
% 7.59/1.52  --qbf_dom_inst                          none
% 7.59/1.52  --qbf_dom_pre_inst                      false
% 7.59/1.52  --qbf_sk_in                             false
% 7.59/1.52  --qbf_pred_elim                         true
% 7.59/1.52  --qbf_split                             512
% 7.59/1.52  
% 7.59/1.52  ------ BMC1 Options
% 7.59/1.52  
% 7.59/1.52  --bmc1_incremental                      false
% 7.59/1.52  --bmc1_axioms                           reachable_all
% 7.59/1.52  --bmc1_min_bound                        0
% 7.59/1.52  --bmc1_max_bound                        -1
% 7.59/1.52  --bmc1_max_bound_default                -1
% 7.59/1.52  --bmc1_symbol_reachability              true
% 7.59/1.52  --bmc1_property_lemmas                  false
% 7.59/1.52  --bmc1_k_induction                      false
% 7.59/1.52  --bmc1_non_equiv_states                 false
% 7.59/1.52  --bmc1_deadlock                         false
% 7.59/1.52  --bmc1_ucm                              false
% 7.59/1.52  --bmc1_add_unsat_core                   none
% 7.59/1.52  --bmc1_unsat_core_children              false
% 7.59/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.52  --bmc1_out_stat                         full
% 7.59/1.52  --bmc1_ground_init                      false
% 7.59/1.52  --bmc1_pre_inst_next_state              false
% 7.59/1.52  --bmc1_pre_inst_state                   false
% 7.59/1.52  --bmc1_pre_inst_reach_state             false
% 7.59/1.52  --bmc1_out_unsat_core                   false
% 7.59/1.52  --bmc1_aig_witness_out                  false
% 7.59/1.52  --bmc1_verbose                          false
% 7.59/1.52  --bmc1_dump_clauses_tptp                false
% 7.59/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.52  --bmc1_dump_file                        -
% 7.59/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.52  --bmc1_ucm_extend_mode                  1
% 7.59/1.52  --bmc1_ucm_init_mode                    2
% 7.59/1.52  --bmc1_ucm_cone_mode                    none
% 7.59/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.52  --bmc1_ucm_relax_model                  4
% 7.59/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.52  --bmc1_ucm_layered_model                none
% 7.59/1.52  --bmc1_ucm_max_lemma_size               10
% 7.59/1.52  
% 7.59/1.52  ------ AIG Options
% 7.59/1.52  
% 7.59/1.52  --aig_mode                              false
% 7.59/1.52  
% 7.59/1.52  ------ Instantiation Options
% 7.59/1.52  
% 7.59/1.52  --instantiation_flag                    true
% 7.59/1.52  --inst_sos_flag                         false
% 7.59/1.52  --inst_sos_phase                        true
% 7.59/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.52  --inst_lit_sel_side                     num_symb
% 7.59/1.52  --inst_solver_per_active                1400
% 7.59/1.52  --inst_solver_calls_frac                1.
% 7.59/1.52  --inst_passive_queue_type               priority_queues
% 7.59/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.52  --inst_passive_queues_freq              [25;2]
% 7.59/1.52  --inst_dismatching                      true
% 7.59/1.52  --inst_eager_unprocessed_to_passive     true
% 7.59/1.52  --inst_prop_sim_given                   true
% 7.59/1.52  --inst_prop_sim_new                     false
% 7.59/1.52  --inst_subs_new                         false
% 7.59/1.52  --inst_eq_res_simp                      false
% 7.59/1.52  --inst_subs_given                       false
% 7.59/1.52  --inst_orphan_elimination               true
% 7.59/1.52  --inst_learning_loop_flag               true
% 7.59/1.52  --inst_learning_start                   3000
% 7.59/1.52  --inst_learning_factor                  2
% 7.59/1.52  --inst_start_prop_sim_after_learn       3
% 7.59/1.52  --inst_sel_renew                        solver
% 7.59/1.52  --inst_lit_activity_flag                true
% 7.59/1.52  --inst_restr_to_given                   false
% 7.59/1.52  --inst_activity_threshold               500
% 7.59/1.52  --inst_out_proof                        true
% 7.59/1.52  
% 7.59/1.52  ------ Resolution Options
% 7.59/1.52  
% 7.59/1.52  --resolution_flag                       true
% 7.59/1.52  --res_lit_sel                           adaptive
% 7.59/1.52  --res_lit_sel_side                      none
% 7.59/1.52  --res_ordering                          kbo
% 7.59/1.52  --res_to_prop_solver                    active
% 7.59/1.52  --res_prop_simpl_new                    false
% 7.59/1.52  --res_prop_simpl_given                  true
% 7.59/1.52  --res_passive_queue_type                priority_queues
% 7.59/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.52  --res_passive_queues_freq               [15;5]
% 7.59/1.52  --res_forward_subs                      full
% 7.59/1.52  --res_backward_subs                     full
% 7.59/1.52  --res_forward_subs_resolution           true
% 7.59/1.52  --res_backward_subs_resolution          true
% 7.59/1.52  --res_orphan_elimination                true
% 7.59/1.52  --res_time_limit                        2.
% 7.59/1.52  --res_out_proof                         true
% 7.59/1.52  
% 7.59/1.52  ------ Superposition Options
% 7.59/1.52  
% 7.59/1.52  --superposition_flag                    true
% 7.59/1.52  --sup_passive_queue_type                priority_queues
% 7.59/1.52  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.52  --sup_passive_queues_freq               [1;4]
% 7.59/1.52  --demod_completeness_check              fast
% 7.59/1.52  --demod_use_ground                      true
% 7.59/1.52  --sup_to_prop_solver                    passive
% 7.59/1.52  --sup_prop_simpl_new                    true
% 7.59/1.52  --sup_prop_simpl_given                  true
% 7.59/1.52  --sup_fun_splitting                     false
% 7.59/1.52  --sup_smt_interval                      50000
% 7.59/1.52  
% 7.59/1.52  ------ Superposition Simplification Setup
% 7.59/1.52  
% 7.59/1.52  --sup_indices_passive                   []
% 7.59/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.52  --sup_full_bw                           [BwDemod]
% 7.59/1.52  --sup_immed_triv                        [TrivRules]
% 7.59/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.52  --sup_immed_bw_main                     []
% 7.59/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.52  
% 7.59/1.52  ------ Combination Options
% 7.59/1.52  
% 7.59/1.52  --comb_res_mult                         3
% 7.59/1.52  --comb_sup_mult                         2
% 7.59/1.52  --comb_inst_mult                        10
% 7.59/1.52  
% 7.59/1.52  ------ Debug Options
% 7.59/1.52  
% 7.59/1.52  --dbg_backtrace                         false
% 7.59/1.52  --dbg_dump_prop_clauses                 false
% 7.59/1.52  --dbg_dump_prop_clauses_file            -
% 7.59/1.52  --dbg_out_stat                          false
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  ------ Proving...
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  % SZS status Theorem for theBenchmark.p
% 7.59/1.52  
% 7.59/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.52  
% 7.59/1.52  fof(f4,axiom,(
% 7.59/1.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f32,plain,(
% 7.59/1.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.59/1.52    inference(cnf_transformation,[],[f4])).
% 7.59/1.52  
% 7.59/1.52  fof(f3,axiom,(
% 7.59/1.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f12,plain,(
% 7.59/1.52    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 7.59/1.52    inference(unused_predicate_definition_removal,[],[f3])).
% 7.59/1.52  
% 7.59/1.52  fof(f13,plain,(
% 7.59/1.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 7.59/1.52    inference(ennf_transformation,[],[f12])).
% 7.59/1.52  
% 7.59/1.52  fof(f31,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.59/1.52    inference(cnf_transformation,[],[f13])).
% 7.59/1.52  
% 7.59/1.52  fof(f2,axiom,(
% 7.59/1.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f11,plain,(
% 7.59/1.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.59/1.52    inference(rectify,[],[f2])).
% 7.59/1.52  
% 7.59/1.52  fof(f30,plain,(
% 7.59/1.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.59/1.52    inference(cnf_transformation,[],[f11])).
% 7.59/1.52  
% 7.59/1.52  fof(f5,axiom,(
% 7.59/1.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f33,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.59/1.52    inference(cnf_transformation,[],[f5])).
% 7.59/1.52  
% 7.59/1.52  fof(f40,plain,(
% 7.59/1.52    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 7.59/1.52    inference(definition_unfolding,[],[f30,f33])).
% 7.59/1.52  
% 7.59/1.52  fof(f1,axiom,(
% 7.59/1.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f17,plain,(
% 7.59/1.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.59/1.52    inference(nnf_transformation,[],[f1])).
% 7.59/1.52  
% 7.59/1.52  fof(f18,plain,(
% 7.59/1.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.59/1.52    inference(flattening,[],[f17])).
% 7.59/1.52  
% 7.59/1.52  fof(f19,plain,(
% 7.59/1.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.59/1.52    inference(rectify,[],[f18])).
% 7.59/1.52  
% 7.59/1.52  fof(f20,plain,(
% 7.59/1.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.59/1.52    introduced(choice_axiom,[])).
% 7.59/1.52  
% 7.59/1.52  fof(f21,plain,(
% 7.59/1.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.59/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 7.59/1.52  
% 7.59/1.52  fof(f27,plain,(
% 7.59/1.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.59/1.52    inference(cnf_transformation,[],[f21])).
% 7.59/1.52  
% 7.59/1.52  fof(f28,plain,(
% 7.59/1.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.59/1.52    inference(cnf_transformation,[],[f21])).
% 7.59/1.52  
% 7.59/1.52  fof(f25,plain,(
% 7.59/1.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.59/1.52    inference(cnf_transformation,[],[f21])).
% 7.59/1.52  
% 7.59/1.52  fof(f44,plain,(
% 7.59/1.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.59/1.52    inference(equality_resolution,[],[f25])).
% 7.59/1.52  
% 7.59/1.52  fof(f7,axiom,(
% 7.59/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f35,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.59/1.52    inference(cnf_transformation,[],[f7])).
% 7.59/1.52  
% 7.59/1.52  fof(f41,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.59/1.52    inference(definition_unfolding,[],[f35,f33])).
% 7.59/1.52  
% 7.59/1.52  fof(f6,axiom,(
% 7.59/1.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f34,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.59/1.52    inference(cnf_transformation,[],[f6])).
% 7.59/1.52  
% 7.59/1.52  fof(f24,plain,(
% 7.59/1.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.59/1.52    inference(cnf_transformation,[],[f21])).
% 7.59/1.52  
% 7.59/1.52  fof(f45,plain,(
% 7.59/1.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.59/1.52    inference(equality_resolution,[],[f24])).
% 7.59/1.52  
% 7.59/1.52  fof(f9,conjecture,(
% 7.59/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f10,negated_conjecture,(
% 7.59/1.52    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.59/1.52    inference(negated_conjecture,[],[f9])).
% 7.59/1.52  
% 7.59/1.52  fof(f15,plain,(
% 7.59/1.52    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 7.59/1.52    inference(ennf_transformation,[],[f10])).
% 7.59/1.52  
% 7.59/1.52  fof(f16,plain,(
% 7.59/1.52    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 7.59/1.52    inference(flattening,[],[f15])).
% 7.59/1.52  
% 7.59/1.52  fof(f22,plain,(
% 7.59/1.52    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k7_relat_1(sK2,sK1)) != sK1 & r1_tarski(sK1,k1_relat_1(sK2)) & v1_relat_1(sK2))),
% 7.59/1.52    introduced(choice_axiom,[])).
% 7.59/1.52  
% 7.59/1.52  fof(f23,plain,(
% 7.59/1.52    k1_relat_1(k7_relat_1(sK2,sK1)) != sK1 & r1_tarski(sK1,k1_relat_1(sK2)) & v1_relat_1(sK2)),
% 7.59/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f22])).
% 7.59/1.52  
% 7.59/1.52  fof(f37,plain,(
% 7.59/1.52    v1_relat_1(sK2)),
% 7.59/1.52    inference(cnf_transformation,[],[f23])).
% 7.59/1.52  
% 7.59/1.52  fof(f8,axiom,(
% 7.59/1.52    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f14,plain,(
% 7.59/1.52    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.59/1.52    inference(ennf_transformation,[],[f8])).
% 7.59/1.52  
% 7.59/1.52  fof(f36,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.59/1.52    inference(cnf_transformation,[],[f14])).
% 7.59/1.52  
% 7.59/1.52  fof(f42,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.59/1.52    inference(definition_unfolding,[],[f36,f33])).
% 7.59/1.52  
% 7.59/1.52  fof(f38,plain,(
% 7.59/1.52    r1_tarski(sK1,k1_relat_1(sK2))),
% 7.59/1.52    inference(cnf_transformation,[],[f23])).
% 7.59/1.52  
% 7.59/1.52  fof(f39,plain,(
% 7.59/1.52    k1_relat_1(k7_relat_1(sK2,sK1)) != sK1),
% 7.59/1.52    inference(cnf_transformation,[],[f23])).
% 7.59/1.52  
% 7.59/1.52  cnf(c_8,plain,
% 7.59/1.52      ( r1_tarski(k1_xboole_0,X0) ),
% 7.59/1.52      inference(cnf_transformation,[],[f32]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_319,plain,
% 7.59/1.52      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.59/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_7,plain,
% 7.59/1.52      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.59/1.52      inference(cnf_transformation,[],[f31]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_320,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.59/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.59/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_685,plain,
% 7.59/1.52      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_319,c_320]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_6,plain,
% 7.59/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.59/1.52      inference(cnf_transformation,[],[f40]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_2,plain,
% 7.59/1.52      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.59/1.52      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.59/1.52      | k4_xboole_0(X0,X1) = X2 ),
% 7.59/1.52      inference(cnf_transformation,[],[f27]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_324,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X1) = X2
% 7.59/1.52      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.59/1.52      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.59/1.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_1,plain,
% 7.59/1.52      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.59/1.52      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.59/1.52      | k4_xboole_0(X0,X1) = X2 ),
% 7.59/1.52      inference(cnf_transformation,[],[f28]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_325,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X1) = X2
% 7.59/1.52      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 7.59/1.52      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.59/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_4608,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X0) = X1
% 7.59/1.52      | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_324,c_325]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_4,plain,
% 7.59/1.52      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.59/1.52      inference(cnf_transformation,[],[f44]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_322,plain,
% 7.59/1.52      ( r2_hidden(X0,X1) != iProver_top
% 7.59/1.52      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.59/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_7214,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
% 7.59/1.52      | r2_hidden(sK0(X0,X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_4608,c_322]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_11869,plain,
% 7.59/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X1,X1)
% 7.59/1.52      | r2_hidden(sK0(X1,X1,X0),k4_xboole_0(X0,X0)) != iProver_top ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_6,c_7214]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_11948,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X0) = X1
% 7.59/1.52      | r2_hidden(sK0(X0,X0,X1),k4_xboole_0(X1,X1)) != iProver_top ),
% 7.59/1.52      inference(demodulation,[status(thm)],[c_11869,c_6]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_12305,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X0) = k1_xboole_0
% 7.59/1.52      | r2_hidden(sK0(X0,X0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_685,c_11948]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_10,plain,
% 7.59/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 7.59/1.52      inference(cnf_transformation,[],[f41]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_5209,plain,
% 7.59/1.52      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_685,c_10]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_9,plain,
% 7.59/1.52      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.59/1.52      inference(cnf_transformation,[],[f34]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_505,plain,
% 7.59/1.52      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_10,c_10]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_791,plain,
% 7.59/1.52      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_9,c_505]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_5589,plain,
% 7.59/1.52      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_5209,c_791]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_793,plain,
% 7.59/1.52      ( k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1)))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_505,c_10]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_6511,plain,
% 7.59/1.52      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_5589,c_793]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_5575,plain,
% 7.59/1.52      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_9,c_5209]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_6549,plain,
% 7.59/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.59/1.52      inference(light_normalisation,[status(thm)],[c_6511,c_5575]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_5,plain,
% 7.59/1.52      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.59/1.52      inference(cnf_transformation,[],[f45]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_321,plain,
% 7.59/1.52      ( r2_hidden(X0,X1) = iProver_top
% 7.59/1.52      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 7.59/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_7213,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
% 7.59/1.52      | r2_hidden(sK0(X0,X0,k4_xboole_0(X1,X2)),X1) = iProver_top ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_4608,c_321]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_10602,plain,
% 7.59/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X1,X1)
% 7.59/1.52      | r2_hidden(sK0(X1,X1,k1_xboole_0),X0) = iProver_top ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_6549,c_7213]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_10683,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X0) = k1_xboole_0
% 7.59/1.52      | r2_hidden(sK0(X0,X0,k1_xboole_0),X1) = iProver_top ),
% 7.59/1.52      inference(light_normalisation,[status(thm)],[c_10602,c_6549]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_11871,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X1)
% 7.59/1.52      | r2_hidden(sK0(X0,X0,k1_xboole_0),X1) != iProver_top ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_685,c_7214]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_11940,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X0) = k1_xboole_0
% 7.59/1.52      | r2_hidden(sK0(X0,X0,k1_xboole_0),X1) != iProver_top ),
% 7.59/1.52      inference(demodulation,[status(thm)],[c_11871,c_685]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_12316,plain,
% 7.59/1.52      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.59/1.52      inference(global_propositional_subsumption,
% 7.59/1.52                [status(thm)],
% 7.59/1.52                [c_12305,c_10683,c_11940]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_12328,plain,
% 7.59/1.52      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.59/1.52      inference(demodulation,[status(thm)],[c_12316,c_6]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_12365,plain,
% 7.59/1.52      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 7.59/1.52      inference(instantiation,[status(thm)],[c_12328]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_14,negated_conjecture,
% 7.59/1.52      ( v1_relat_1(sK2) ),
% 7.59/1.52      inference(cnf_transformation,[],[f37]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_316,plain,
% 7.59/1.52      ( v1_relat_1(sK2) = iProver_top ),
% 7.59/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_11,plain,
% 7.59/1.52      ( ~ v1_relat_1(X0)
% 7.59/1.52      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 7.59/1.52      inference(cnf_transformation,[],[f42]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_318,plain,
% 7.59/1.52      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 7.59/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_353,plain,
% 7.59/1.52      ( k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 7.59/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.52      inference(demodulation,[status(thm)],[c_318,c_10]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_786,plain,
% 7.59/1.52      ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_316,c_353]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_1559,plain,
% 7.59/1.52      ( k1_setfam_1(k2_tarski(X0,k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_9,c_786]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_13,negated_conjecture,
% 7.59/1.52      ( r1_tarski(sK1,k1_relat_1(sK2)) ),
% 7.59/1.52      inference(cnf_transformation,[],[f38]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_317,plain,
% 7.59/1.52      ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top ),
% 7.59/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_686,plain,
% 7.59/1.52      ( k4_xboole_0(sK1,k1_relat_1(sK2)) = k1_xboole_0 ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_317,c_320]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_1097,plain,
% 7.59/1.52      ( k1_setfam_1(k2_tarski(sK1,k1_relat_1(sK2))) = k4_xboole_0(sK1,k1_xboole_0) ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_686,c_10]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_1611,plain,
% 7.59/1.52      ( k1_relat_1(k7_relat_1(sK2,sK1)) = k4_xboole_0(sK1,k1_xboole_0) ),
% 7.59/1.52      inference(superposition,[status(thm)],[c_1559,c_1097]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_12,negated_conjecture,
% 7.59/1.52      ( k1_relat_1(k7_relat_1(sK2,sK1)) != sK1 ),
% 7.59/1.52      inference(cnf_transformation,[],[f39]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(c_5985,plain,
% 7.59/1.52      ( k4_xboole_0(sK1,k1_xboole_0) != sK1 ),
% 7.59/1.52      inference(demodulation,[status(thm)],[c_1611,c_12]) ).
% 7.59/1.52  
% 7.59/1.52  cnf(contradiction,plain,
% 7.59/1.52      ( $false ),
% 7.59/1.52      inference(minisat,[status(thm)],[c_12365,c_5985]) ).
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.59/1.52  
% 7.59/1.52  ------                               Statistics
% 7.59/1.52  
% 7.59/1.52  ------ Selected
% 7.59/1.52  
% 7.59/1.52  total_time:                             0.513
% 7.59/1.52  
%------------------------------------------------------------------------------
