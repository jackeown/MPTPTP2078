%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 120 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  240 ( 451 expanded)
%              Number of equality atoms :   56 ( 107 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(subsumption_resolution,[],[f122,f93])).

fof(f93,plain,(
    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f32,f92])).

fof(f92,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f91,f60])).

fof(f60,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f56,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f56,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f91,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | r2_hidden(k4_tarski(sK4(sK0,k1_xboole_0,sK5(k5_relat_1(sK0,k1_xboole_0)),sK6(k5_relat_1(sK0,k1_xboole_0))),sK6(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) ),
    inference(resolution,[],[f86,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k5_relat_1(sK0,X0)
      | r2_hidden(k4_tarski(sK4(sK0,X0,sK5(k5_relat_1(sK0,X0)),sK6(k5_relat_1(sK0,X0))),sK6(k5_relat_1(sK0,X0))),X0) ) ),
    inference(resolution,[],[f82,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(sK0,X0,sK5(k5_relat_1(sK0,X0)),sK6(k5_relat_1(sK0,X0))),sK6(k5_relat_1(sK0,X0))),X0)
      | k1_xboole_0 = k5_relat_1(sK0,X0) ) ),
    inference(resolution,[],[f66,f31])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK4(X0,X1,sK5(k5_relat_1(X0,X1)),sK6(k5_relat_1(X0,X1))),sK6(k5_relat_1(X0,X1))),X1)
      | k1_xboole_0 = k5_relat_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f65,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,sK5(k5_relat_1(X0,X1)),sK6(k5_relat_1(X0,X1))),sK6(k5_relat_1(X0,X1))),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X0,X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f58,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f54,f33])).

fof(f54,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f32,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f122,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f121,f31])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f120,f60])).

fof(f120,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK5(k5_relat_1(k1_xboole_0,X0)),sK4(k1_xboole_0,X0,sK5(k5_relat_1(k1_xboole_0,X0)),sK6(k5_relat_1(k1_xboole_0,X0)))),k1_xboole_0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f98,f42])).

fof(f98,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | r2_hidden(k4_tarski(sK5(k5_relat_1(X2,X1)),sK4(X2,X1,sK5(k5_relat_1(X2,X1)),sK6(k5_relat_1(X2,X1)))),X2)
      | k1_xboole_0 = k5_relat_1(X2,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f68,f43])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK5(k5_relat_1(X0,X1)),sK4(X0,X1,sK5(k5_relat_1(X0,X1)),sK6(k5_relat_1(X0,X1)))),X0)
      | k1_xboole_0 = k5_relat_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f67,f33])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(k5_relat_1(X0,X1)),sK4(X0,X1,sK5(k5_relat_1(X0,X1)),sK6(k5_relat_1(X0,X1)))),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X0,X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f59,f40])).

fof(f59,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f55,f33])).

fof(f55,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:33:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (4884)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (4876)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (4873)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (4884)Refutation not found, incomplete strategy% (4884)------------------------------
% 0.21/0.52  % (4884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4884)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4884)Memory used [KB]: 10618
% 0.21/0.52  % (4884)Time elapsed: 0.106 s
% 0.21/0.52  % (4884)------------------------------
% 0.21/0.52  % (4884)------------------------------
% 0.21/0.52  % (4871)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (4870)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (4892)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (4867)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (4887)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (4868)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (4887)Refutation not found, incomplete strategy% (4887)------------------------------
% 0.21/0.52  % (4887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4887)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4887)Memory used [KB]: 10746
% 0.21/0.52  % (4887)Time elapsed: 0.108 s
% 0.21/0.52  % (4887)------------------------------
% 0.21/0.52  % (4887)------------------------------
% 0.21/0.53  % (4879)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (4880)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (4872)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (4886)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (4874)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (4890)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (4872)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f32,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f91,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(superposition,[],[f56,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f45,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f47,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.53    inference(flattening,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.53    inference(nnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | r2_hidden(k4_tarski(sK4(sK0,k1_xboole_0,sK5(k5_relat_1(sK0,k1_xboole_0)),sK6(k5_relat_1(sK0,k1_xboole_0))),sK6(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0)),
% 0.21/0.53    inference(resolution,[],[f86,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k5_relat_1(sK0,X0) | r2_hidden(k4_tarski(sK4(sK0,X0,sK5(k5_relat_1(sK0,X0)),sK6(k5_relat_1(sK0,X0))),sK6(k5_relat_1(sK0,X0))),X0)) )),
% 0.21/0.53    inference(resolution,[],[f82,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(sK0,X0,sK5(k5_relat_1(sK0,X0)),sK6(k5_relat_1(sK0,X0))),sK6(k5_relat_1(sK0,X0))),X0) | k1_xboole_0 = k5_relat_1(sK0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f66,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    v1_relat_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK4(X0,X1,sK5(k5_relat_1(X0,X1)),sK6(k5_relat_1(X0,X1))),sK6(k5_relat_1(X0,X1))),X1) | k1_xboole_0 = k5_relat_1(X0,X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f65,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,sK5(k5_relat_1(X0,X1)),sK6(k5_relat_1(X0,X1))),sK6(k5_relat_1(X0,X1))),X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,X1) | ~v1_relat_1(k5_relat_1(X0,X1))) )),
% 0.21/0.53    inference(resolution,[],[f58,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f54,f33])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f25,f24,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(rectify,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(resolution,[],[f121,f31])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f120,f60])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(k4_tarski(sK5(k5_relat_1(k1_xboole_0,X0)),sK4(k1_xboole_0,X0,sK5(k5_relat_1(k1_xboole_0,X0)),sK6(k5_relat_1(k1_xboole_0,X0)))),k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(resolution,[],[f98,f42])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~v1_xboole_0(X2) | r2_hidden(k4_tarski(sK5(k5_relat_1(X2,X1)),sK4(X2,X1,sK5(k5_relat_1(X2,X1)),sK6(k5_relat_1(X2,X1)))),X2) | k1_xboole_0 = k5_relat_1(X2,X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(resolution,[],[f68,f43])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK5(k5_relat_1(X0,X1)),sK4(X0,X1,sK5(k5_relat_1(X0,X1)),sK6(k5_relat_1(X0,X1)))),X0) | k1_xboole_0 = k5_relat_1(X0,X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f67,f33])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(k5_relat_1(X0,X1)),sK4(X0,X1,sK5(k5_relat_1(X0,X1)),sK6(k5_relat_1(X0,X1)))),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,X1) | ~v1_relat_1(k5_relat_1(X0,X1))) )),
% 0.21/0.53    inference(resolution,[],[f59,f40])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f55,f33])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (4872)------------------------------
% 0.21/0.53  % (4872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4872)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (4872)Memory used [KB]: 6396
% 0.21/0.53  % (4872)Time elapsed: 0.121 s
% 0.21/0.53  % (4872)------------------------------
% 0.21/0.53  % (4872)------------------------------
% 0.21/0.53  % (4889)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (4866)Success in time 0.174 s
%------------------------------------------------------------------------------
