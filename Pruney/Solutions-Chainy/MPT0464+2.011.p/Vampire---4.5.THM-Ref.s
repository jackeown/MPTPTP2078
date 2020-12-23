%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:26 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 461 expanded)
%              Number of leaves         :   29 ( 153 expanded)
%              Depth                    :   16
%              Number of atoms          :  268 ( 812 expanded)
%              Number of equality atoms :   38 ( 311 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f251,f307,f398])).

fof(f398,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | spl5_11 ),
    inference(subsumption_resolution,[],[f333,f384])).

fof(f384,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) ),
    inference(forward_demodulation,[],[f383,f356])).

fof(f356,plain,(
    ! [X1] : k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(forward_demodulation,[],[f353,f283])).

fof(f283,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(resolution,[],[f276,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f70,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f276,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f275,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f275,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k5_xboole_0(X9,X9)) ),
    inference(subsumption_resolution,[],[f271,f143])).

fof(f143,plain,(
    ! [X1] : r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(superposition,[],[f87,f85])).

fof(f85,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f80])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f58,f81])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f63,f80])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f271,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,k5_xboole_0(X9,X9))
      | ~ r1_tarski(k5_xboole_0(X9,X9),X9) ) ),
    inference(resolution,[],[f177,f137])).

fof(f137,plain,(
    ! [X1] : r1_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(superposition,[],[f86,f85])).

fof(f86,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) ),
    inference(definition_unfolding,[],[f57,f81])).

fof(f57,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f177,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ r2_hidden(X4,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f90,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f80])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f80])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f353,plain,(
    ! [X1] : k3_tarski(k2_enumset1(X1,X1,X1,k5_xboole_0(X1,X1))) = X1 ),
    inference(superposition,[],[f89,f85])).

fof(f89,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f64,f82,f80,f81])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f61,f79])).

fof(f61,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f383,plain,(
    ! [X0,X1] : r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_xboole_0)),X1) ),
    inference(forward_demodulation,[],[f375,f356])).

fof(f375,plain,(
    ! [X0,X1] : r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_xboole_0)),k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0))) ),
    inference(superposition,[],[f93,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f53,f80])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f93,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f77,f82,f80,f80,f82])).

fof(f77,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f333,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
    | spl5_11 ),
    inference(subsumption_resolution,[],[f332,f50])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(f332,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK2)
    | spl5_11 ),
    inference(subsumption_resolution,[],[f329,f48])).

fof(f48,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f329,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | spl5_11 ),
    inference(resolution,[],[f250,f266])).

fof(f266,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f54,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f55,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(f250,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl5_11
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f307,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl5_7 ),
    inference(subsumption_resolution,[],[f305,f49])).

fof(f49,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f305,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f304,f48])).

fof(f304,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f301,f88])).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f59,f80])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f301,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | spl5_7 ),
    inference(resolution,[],[f266,f191])).

fof(f191,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl5_7
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f251,plain,
    ( ~ spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f241,f248,f189])).

fof(f241,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f94,f83])).

% (25996)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (26001)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (26010)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (26000)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (26007)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (25995)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (25993)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (25991)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (25999)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f83,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k1_setfam_1(k2_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f51,f80,f80])).

fof(f51,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f80])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:18:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.56  % (25984)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.54/0.57  % (26008)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.54/0.57  % (26005)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.54/0.57  % (25997)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.54/0.58  % (25984)Refutation not found, incomplete strategy% (25984)------------------------------
% 1.54/0.58  % (25984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (25984)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (25984)Memory used [KB]: 10746
% 1.54/0.58  % (25984)Time elapsed: 0.131 s
% 1.54/0.58  % (25984)------------------------------
% 1.54/0.58  % (25984)------------------------------
% 1.54/0.58  % (25989)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.70/0.59  % (25992)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.70/0.59  % (25992)Refutation not found, incomplete strategy% (25992)------------------------------
% 1.70/0.59  % (25992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (25992)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.59  
% 1.70/0.59  % (25992)Memory used [KB]: 10618
% 1.70/0.59  % (25992)Time elapsed: 0.142 s
% 1.70/0.59  % (25992)------------------------------
% 1.70/0.59  % (25992)------------------------------
% 1.70/0.60  % (25994)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.70/0.60  % (25985)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.70/0.61  % (25987)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.70/0.62  % (25982)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.70/0.62  % (25988)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.70/0.63  % (25986)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.70/0.63  % (26011)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.70/0.63  % (26004)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.70/0.63  % (26006)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.70/0.63  % (26004)Refutation not found, incomplete strategy% (26004)------------------------------
% 1.70/0.63  % (26004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.63  % (26004)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.63  
% 1.70/0.63  % (26004)Memory used [KB]: 10746
% 1.70/0.63  % (26004)Time elapsed: 0.185 s
% 1.70/0.63  % (26004)------------------------------
% 1.70/0.63  % (26004)------------------------------
% 1.70/0.63  % (26009)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.70/0.63  % (25998)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.70/0.63  % (25983)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.70/0.64  % (25990)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.70/0.64  % (26003)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.70/0.64  % (26002)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.70/0.64  % (26003)Refutation not found, incomplete strategy% (26003)------------------------------
% 1.70/0.64  % (26003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.64  % (26003)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.64  
% 1.70/0.64  % (26003)Memory used [KB]: 1663
% 1.70/0.64  % (26003)Time elapsed: 0.194 s
% 1.70/0.64  % (26003)------------------------------
% 1.70/0.64  % (26003)------------------------------
% 1.70/0.64  % (25990)Refutation not found, incomplete strategy% (25990)------------------------------
% 1.70/0.64  % (25990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.64  % (25990)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.64  
% 1.70/0.64  % (25990)Memory used [KB]: 10746
% 1.70/0.64  % (25990)Time elapsed: 0.195 s
% 1.70/0.64  % (25990)------------------------------
% 1.70/0.64  % (25990)------------------------------
% 1.70/0.64  % (26009)Refutation found. Thanks to Tanya!
% 1.70/0.64  % SZS status Theorem for theBenchmark
% 1.70/0.64  % SZS output start Proof for theBenchmark
% 1.70/0.64  fof(f400,plain,(
% 1.70/0.64    $false),
% 1.70/0.64    inference(avatar_sat_refutation,[],[f251,f307,f398])).
% 1.70/0.64  fof(f398,plain,(
% 1.70/0.64    spl5_11),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f389])).
% 1.70/0.64  fof(f389,plain,(
% 1.70/0.64    $false | spl5_11),
% 1.70/0.64    inference(subsumption_resolution,[],[f333,f384])).
% 1.70/0.64  fof(f384,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1)) )),
% 1.70/0.64    inference(forward_demodulation,[],[f383,f356])).
% 1.70/0.64  fof(f356,plain,(
% 1.70/0.64    ( ! [X1] : (k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0)) = X1) )),
% 1.70/0.64    inference(forward_demodulation,[],[f353,f283])).
% 1.70/0.64  fof(f283,plain,(
% 1.70/0.64    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 1.70/0.64    inference(resolution,[],[f276,f125])).
% 1.70/0.64  fof(f125,plain,(
% 1.70/0.64    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.70/0.64    inference(resolution,[],[f70,f52])).
% 1.70/0.64  fof(f52,plain,(
% 1.70/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f10])).
% 1.70/0.64  fof(f10,axiom,(
% 1.70/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.70/0.64  fof(f70,plain,(
% 1.70/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f42])).
% 1.70/0.64  fof(f42,plain,(
% 1.70/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.64    inference(flattening,[],[f41])).
% 1.70/0.64  fof(f41,plain,(
% 1.70/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.64    inference(nnf_transformation,[],[f4])).
% 1.70/0.64  fof(f4,axiom,(
% 1.70/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.70/0.64  fof(f276,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,X0),X1)) )),
% 1.70/0.64    inference(resolution,[],[f275,f72])).
% 1.70/0.64  fof(f72,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f46])).
% 1.70/0.64  fof(f46,plain,(
% 1.70/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.70/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).
% 1.70/0.64  fof(f45,plain,(
% 1.70/0.64    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f44,plain,(
% 1.70/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.70/0.64    inference(rectify,[],[f43])).
% 1.70/0.64  fof(f43,plain,(
% 1.70/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.70/0.64    inference(nnf_transformation,[],[f32])).
% 1.70/0.64  fof(f32,plain,(
% 1.70/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.70/0.64    inference(ennf_transformation,[],[f1])).
% 1.70/0.64  fof(f1,axiom,(
% 1.70/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.70/0.64  fof(f275,plain,(
% 1.70/0.64    ( ! [X8,X9] : (~r2_hidden(X8,k5_xboole_0(X9,X9))) )),
% 1.70/0.64    inference(subsumption_resolution,[],[f271,f143])).
% 1.70/0.64  fof(f143,plain,(
% 1.70/0.64    ( ! [X1] : (r1_tarski(k5_xboole_0(X1,X1),X1)) )),
% 1.70/0.64    inference(superposition,[],[f87,f85])).
% 1.70/0.64  fof(f85,plain,(
% 1.70/0.64    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.70/0.64    inference(definition_unfolding,[],[f56,f80])).
% 1.70/0.64  fof(f80,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.70/0.64    inference(definition_unfolding,[],[f60,f79])).
% 1.70/0.64  fof(f79,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.70/0.64    inference(definition_unfolding,[],[f62,f76])).
% 1.70/0.64  fof(f76,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f16])).
% 1.70/0.64  fof(f16,axiom,(
% 1.70/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.70/0.64  fof(f62,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f15])).
% 1.70/0.64  fof(f15,axiom,(
% 1.70/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.70/0.64  fof(f60,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.70/0.64    inference(cnf_transformation,[],[f18])).
% 1.70/0.64  fof(f18,axiom,(
% 1.70/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.70/0.64  fof(f56,plain,(
% 1.70/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.70/0.64    inference(cnf_transformation,[],[f24])).
% 1.70/0.64  fof(f24,plain,(
% 1.70/0.64    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.70/0.64    inference(rectify,[],[f2])).
% 1.70/0.64  fof(f2,axiom,(
% 1.70/0.64    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.70/0.64  fof(f87,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0)) )),
% 1.70/0.64    inference(definition_unfolding,[],[f58,f81])).
% 1.70/0.64  fof(f81,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.70/0.64    inference(definition_unfolding,[],[f63,f80])).
% 1.70/0.64  fof(f63,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.70/0.64    inference(cnf_transformation,[],[f5])).
% 1.70/0.64  fof(f5,axiom,(
% 1.70/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.70/0.64  fof(f58,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f12])).
% 1.70/0.64  fof(f12,axiom,(
% 1.70/0.64    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.70/0.64  fof(f271,plain,(
% 1.70/0.64    ( ! [X8,X9] : (~r2_hidden(X8,k5_xboole_0(X9,X9)) | ~r1_tarski(k5_xboole_0(X9,X9),X9)) )),
% 1.70/0.64    inference(resolution,[],[f177,f137])).
% 1.70/0.64  fof(f137,plain,(
% 1.70/0.64    ( ! [X1] : (r1_xboole_0(k5_xboole_0(X1,X1),X1)) )),
% 1.70/0.64    inference(superposition,[],[f86,f85])).
% 1.70/0.64  fof(f86,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1)) )),
% 1.70/0.64    inference(definition_unfolding,[],[f57,f81])).
% 1.70/0.64  fof(f57,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f14])).
% 1.70/0.64  fof(f14,axiom,(
% 1.70/0.64    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.70/0.64  fof(f177,plain,(
% 1.70/0.64    ( ! [X4,X2,X3] : (~r1_xboole_0(X2,X3) | ~r2_hidden(X4,X2) | ~r1_tarski(X2,X3)) )),
% 1.70/0.64    inference(superposition,[],[f90,f92])).
% 1.70/0.64  fof(f92,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.70/0.64    inference(definition_unfolding,[],[f67,f80])).
% 1.70/0.64  fof(f67,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f31])).
% 1.70/0.64  fof(f31,plain,(
% 1.70/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.70/0.64    inference(ennf_transformation,[],[f8])).
% 1.70/0.64  fof(f8,axiom,(
% 1.70/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.70/0.64  fof(f90,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.70/0.64    inference(definition_unfolding,[],[f66,f80])).
% 1.70/0.64  fof(f66,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.70/0.64    inference(cnf_transformation,[],[f40])).
% 1.70/0.64  fof(f40,plain,(
% 1.70/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.70/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f39])).
% 1.70/0.64  fof(f39,plain,(
% 1.70/0.64    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f30,plain,(
% 1.70/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.70/0.64    inference(ennf_transformation,[],[f25])).
% 1.70/0.64  fof(f25,plain,(
% 1.70/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.70/0.64    inference(rectify,[],[f3])).
% 1.70/0.64  fof(f3,axiom,(
% 1.70/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.70/0.64  fof(f353,plain,(
% 1.70/0.64    ( ! [X1] : (k3_tarski(k2_enumset1(X1,X1,X1,k5_xboole_0(X1,X1))) = X1) )),
% 1.70/0.64    inference(superposition,[],[f89,f85])).
% 1.70/0.64  fof(f89,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) = X0) )),
% 1.70/0.64    inference(definition_unfolding,[],[f64,f82,f80,f81])).
% 1.70/0.64  fof(f82,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.70/0.64    inference(definition_unfolding,[],[f61,f79])).
% 1.70/0.64  fof(f61,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f17])).
% 1.70/0.64  fof(f17,axiom,(
% 1.70/0.64    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.70/0.64  fof(f64,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.70/0.64    inference(cnf_transformation,[],[f13])).
% 1.70/0.64  fof(f13,axiom,(
% 1.70/0.64    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.70/0.64  fof(f383,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_xboole_0)),X1)) )),
% 1.70/0.64    inference(forward_demodulation,[],[f375,f356])).
% 1.70/0.64  fof(f375,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_xboole_0)),k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0)))) )),
% 1.70/0.64    inference(superposition,[],[f93,f84])).
% 1.70/0.64  fof(f84,plain,(
% 1.70/0.64    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) )),
% 1.70/0.64    inference(definition_unfolding,[],[f53,f80])).
% 1.70/0.64  fof(f53,plain,(
% 1.70/0.64    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f9])).
% 1.70/0.64  fof(f9,axiom,(
% 1.70/0.64    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.70/0.64  fof(f93,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 1.70/0.64    inference(definition_unfolding,[],[f77,f82,f80,f80,f82])).
% 1.70/0.64  fof(f77,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 1.70/0.64    inference(cnf_transformation,[],[f11])).
% 1.70/0.64  fof(f11,axiom,(
% 1.70/0.64    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 1.70/0.64  fof(f333,plain,(
% 1.70/0.64    ~r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2) | spl5_11),
% 1.70/0.64    inference(subsumption_resolution,[],[f332,f50])).
% 1.70/0.64  fof(f50,plain,(
% 1.70/0.64    v1_relat_1(sK2)),
% 1.70/0.64    inference(cnf_transformation,[],[f38])).
% 1.70/0.64  fof(f38,plain,(
% 1.70/0.64    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.70/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f37,f36,f35])).
% 1.70/0.64  fof(f35,plain,(
% 1.70/0.64    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f36,plain,(
% 1.70/0.64    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f37,plain,(
% 1.70/0.64    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f26,plain,(
% 1.70/0.64    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.70/0.64    inference(ennf_transformation,[],[f23])).
% 1.70/0.64  fof(f23,negated_conjecture,(
% 1.70/0.64    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.70/0.64    inference(negated_conjecture,[],[f22])).
% 1.70/0.64  fof(f22,conjecture,(
% 1.70/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).
% 1.70/0.64  fof(f332,plain,(
% 1.70/0.64    ~r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(sK2) | spl5_11),
% 1.70/0.64    inference(subsumption_resolution,[],[f329,f48])).
% 1.70/0.64  fof(f48,plain,(
% 1.70/0.64    v1_relat_1(sK0)),
% 1.70/0.64    inference(cnf_transformation,[],[f38])).
% 1.70/0.64  fof(f329,plain,(
% 1.70/0.64    ~r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | spl5_11),
% 1.70/0.64    inference(resolution,[],[f250,f266])).
% 1.70/0.64  fof(f266,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.70/0.64    inference(subsumption_resolution,[],[f54,f98])).
% 1.70/0.64  fof(f98,plain,(
% 1.70/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 1.70/0.64    inference(resolution,[],[f55,f75])).
% 1.70/0.64  fof(f75,plain,(
% 1.70/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f47])).
% 1.70/0.64  fof(f47,plain,(
% 1.70/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.70/0.64    inference(nnf_transformation,[],[f19])).
% 1.70/0.64  fof(f19,axiom,(
% 1.70/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.70/0.64  fof(f55,plain,(
% 1.70/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f29])).
% 1.70/0.64  fof(f29,plain,(
% 1.70/0.64    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.70/0.64    inference(ennf_transformation,[],[f20])).
% 1.70/0.64  fof(f20,axiom,(
% 1.70/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.70/0.64  fof(f54,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f28])).
% 1.70/0.64  fof(f28,plain,(
% 1.70/0.64    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.70/0.64    inference(flattening,[],[f27])).
% 1.70/0.64  fof(f27,plain,(
% 1.70/0.64    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.70/0.64    inference(ennf_transformation,[],[f21])).
% 1.70/0.64  fof(f21,axiom,(
% 1.70/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
% 1.70/0.64  fof(f250,plain,(
% 1.70/0.64    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | spl5_11),
% 1.70/0.64    inference(avatar_component_clause,[],[f248])).
% 1.70/0.64  fof(f248,plain,(
% 1.70/0.64    spl5_11 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.70/0.64  fof(f307,plain,(
% 1.70/0.64    spl5_7),
% 1.70/0.64    inference(avatar_contradiction_clause,[],[f306])).
% 1.70/0.64  fof(f306,plain,(
% 1.70/0.64    $false | spl5_7),
% 1.70/0.64    inference(subsumption_resolution,[],[f305,f49])).
% 1.70/0.64  fof(f49,plain,(
% 1.70/0.64    v1_relat_1(sK1)),
% 1.70/0.64    inference(cnf_transformation,[],[f38])).
% 1.70/0.64  fof(f305,plain,(
% 1.70/0.64    ~v1_relat_1(sK1) | spl5_7),
% 1.70/0.64    inference(subsumption_resolution,[],[f304,f48])).
% 1.70/0.64  fof(f304,plain,(
% 1.70/0.64    ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | spl5_7),
% 1.70/0.64    inference(subsumption_resolution,[],[f301,f88])).
% 1.70/0.64  fof(f88,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.70/0.64    inference(definition_unfolding,[],[f59,f80])).
% 1.70/0.64  fof(f59,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f6])).
% 1.70/0.64  fof(f6,axiom,(
% 1.70/0.64    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.70/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.70/0.64  fof(f301,plain,(
% 1.70/0.64    ~r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | spl5_7),
% 1.70/0.64    inference(resolution,[],[f266,f191])).
% 1.70/0.64  fof(f191,plain,(
% 1.70/0.64    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | spl5_7),
% 1.70/0.64    inference(avatar_component_clause,[],[f189])).
% 1.70/0.64  fof(f189,plain,(
% 1.70/0.64    spl5_7 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.70/0.64  fof(f251,plain,(
% 1.70/0.64    ~spl5_7 | ~spl5_11),
% 1.70/0.64    inference(avatar_split_clause,[],[f241,f248,f189])).
% 1.70/0.64  fof(f241,plain,(
% 1.70/0.64    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.70/0.64    inference(resolution,[],[f94,f83])).
% 1.70/0.64  % (25996)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.70/0.64  % (26001)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.70/0.64  % (26010)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.70/0.65  % (26000)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.70/0.65  % (26007)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.70/0.65  % (25995)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.70/0.65  % (25993)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.21/0.65  % (25991)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.21/0.66  % (25999)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.21/0.66  fof(f83,plain,(
% 2.21/0.66    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k1_setfam_1(k2_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 2.21/0.66    inference(definition_unfolding,[],[f51,f80,f80])).
% 2.21/0.66  fof(f51,plain,(
% 2.21/0.66    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 2.21/0.66    inference(cnf_transformation,[],[f38])).
% 2.21/0.66  fof(f94,plain,(
% 2.21/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.21/0.66    inference(definition_unfolding,[],[f78,f80])).
% 2.21/0.66  fof(f78,plain,(
% 2.21/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.21/0.66    inference(cnf_transformation,[],[f34])).
% 2.21/0.66  fof(f34,plain,(
% 2.21/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.21/0.66    inference(flattening,[],[f33])).
% 2.21/0.66  fof(f33,plain,(
% 2.21/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.21/0.66    inference(ennf_transformation,[],[f7])).
% 2.21/0.66  fof(f7,axiom,(
% 2.21/0.66    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.21/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 2.21/0.66  % SZS output end Proof for theBenchmark
% 2.21/0.66  % (26009)------------------------------
% 2.21/0.66  % (26009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.66  % (26009)Termination reason: Refutation
% 2.21/0.66  
% 2.21/0.66  % (26009)Memory used [KB]: 6396
% 2.21/0.66  % (26009)Time elapsed: 0.202 s
% 2.21/0.66  % (26009)------------------------------
% 2.21/0.66  % (26009)------------------------------
% 2.21/0.66  % (25999)Refutation not found, incomplete strategy% (25999)------------------------------
% 2.21/0.66  % (25999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.66  % (25999)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.66  
% 2.21/0.66  % (25999)Memory used [KB]: 10618
% 2.21/0.66  % (25999)Time elapsed: 0.212 s
% 2.21/0.66  % (25999)------------------------------
% 2.21/0.66  % (25999)------------------------------
% 2.21/0.66  % (25981)Success in time 0.291 s
%------------------------------------------------------------------------------
