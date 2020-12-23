%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:57 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 282 expanded)
%              Number of leaves         :   20 (  86 expanded)
%              Depth                    :   22
%              Number of atoms          :  305 ( 763 expanded)
%              Number of equality atoms :   88 ( 305 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1220,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1199])).

fof(f1199,plain,(
    k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(superposition,[],[f646,f1178])).

fof(f1178,plain,(
    k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f1161,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1161,plain,
    ( ~ r1_tarski(sK2,sK2)
    | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f1081,f78])).

fof(f78,plain,(
    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f46,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( k2_relat_1(sK2) != k1_tarski(sK1)
      | k1_tarski(sK0) != k1_relat_1(sK2) )
    & sK2 = k1_tarski(k4_tarski(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2
        & v1_relat_1(X2) )
   => ( ( k2_relat_1(sK2) != k1_tarski(sK1)
        | k1_tarski(sK0) != k1_relat_1(sK2) )
      & sK2 = k1_tarski(k4_tarski(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k2_relat_1(X2) = k1_tarski(X1)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f1081,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_enumset1(X3,X3,X3,k4_tarski(X4,sK1)),sK2)
      | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ) ),
    inference(resolution,[],[f1073,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f1073,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK1),sK2)
      | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ) ),
    inference(resolution,[],[f1072,f84])).

fof(f84,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1072,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f1070])).

fof(f1070,plain,
    ( k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r2_hidden(sK1,k2_relat_1(sK2))
    | ~ r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f1068,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f64,f75])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1068,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_relat_1(sK2))
    | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f1067,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f1067,plain,(
    ~ r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f1061])).

fof(f1061,plain,
    ( ~ r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_relat_1(sK2))
    | ~ r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_relat_1(sK2)) ),
    inference(resolution,[],[f1050,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK9(X0,X1),X0)
        & r2_hidden(sK9(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f20,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK9(X0,X1),X0)
        & r2_hidden(sK9(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f1050,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK9(k2_enumset1(sK1,sK1,sK1,sK1),X2),k2_relat_1(sK2))
      | ~ r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X2) ) ),
    inference(resolution,[],[f234,f85])).

fof(f85,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK9(k2_enumset1(sK1,sK1,sK1,sK1),X1)),sK2)
      | ~ r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X1) ) ),
    inference(superposition,[],[f104,f210])).

fof(f210,plain,(
    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f79,f78])).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f57,f75,f76,f75])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK9(X1,X2)),k2_zfmisc_1(X3,X1))
      | ~ r2_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f60,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f646,plain,(
    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(trivial_inequality_removal,[],[f637])).

fof(f637,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f77,f635])).

fof(f635,plain,(
    k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f616,f89])).

fof(f616,plain,
    ( ~ r1_tarski(sK2,sK2)
    | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f484,f78])).

fof(f484,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_enumset1(X2,X2,X2,k4_tarski(sK0,X3)),sK2)
      | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ) ),
    inference(resolution,[],[f466,f82])).

fof(f466,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK0,X0),sK2)
      | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ) ),
    inference(resolution,[],[f465,f86])).

fof(f86,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f465,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f463])).

fof(f463,plain,
    ( k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f443,f81])).

fof(f443,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK2))
    | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f421,f70])).

fof(f421,plain,(
    ~ r2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f415])).

fof(f415,plain,
    ( ~ r2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK2))
    | ~ r2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK2)) ),
    inference(resolution,[],[f410,f65])).

fof(f410,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(k2_enumset1(sK0,sK0,sK0,sK0),X0),k1_relat_1(sK2))
      | ~ r2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0) ) ),
    inference(resolution,[],[f214,f87])).

fof(f87,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK9(k2_enumset1(sK0,sK0,sK0,sK0),X0),X1),sK2)
      | ~ r2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0) ) ),
    inference(superposition,[],[f101,f210])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK9(X0,X1),X2),k2_zfmisc_1(X0,X3))
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f59,f66])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,
    ( k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f47,f76,f76])).

fof(f47,plain,
    ( k2_relat_1(sK2) != k1_tarski(sK1)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:58:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (1214)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.50  % (1213)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (1214)Refutation not found, incomplete strategy% (1214)------------------------------
% 0.21/0.51  % (1214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1214)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1214)Memory used [KB]: 1663
% 0.21/0.51  % (1214)Time elapsed: 0.097 s
% 0.21/0.51  % (1214)------------------------------
% 0.21/0.51  % (1214)------------------------------
% 0.21/0.51  % (1218)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (1215)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (1217)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (1221)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (1222)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (1219)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (1236)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (1242)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (1242)Refutation not found, incomplete strategy% (1242)------------------------------
% 0.21/0.53  % (1242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1242)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1242)Memory used [KB]: 1663
% 0.21/0.53  % (1242)Time elapsed: 0.118 s
% 0.21/0.53  % (1242)------------------------------
% 0.21/0.53  % (1242)------------------------------
% 0.21/0.53  % (1228)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (1223)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (1227)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (1231)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (1225)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (1216)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (1239)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (1241)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (1234)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (1235)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (1239)Refutation not found, incomplete strategy% (1239)------------------------------
% 0.21/0.54  % (1239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1239)Memory used [KB]: 6268
% 0.21/0.54  % (1239)Time elapsed: 0.128 s
% 0.21/0.54  % (1239)------------------------------
% 0.21/0.54  % (1239)------------------------------
% 0.21/0.54  % (1229)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (1227)Refutation not found, incomplete strategy% (1227)------------------------------
% 0.21/0.54  % (1227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1227)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1227)Memory used [KB]: 1663
% 0.21/0.54  % (1227)Time elapsed: 0.132 s
% 0.21/0.54  % (1227)------------------------------
% 0.21/0.54  % (1227)------------------------------
% 0.21/0.54  % (1229)Refutation not found, incomplete strategy% (1229)------------------------------
% 0.21/0.54  % (1229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1229)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1229)Memory used [KB]: 10618
% 0.21/0.54  % (1229)Time elapsed: 0.121 s
% 0.21/0.54  % (1229)------------------------------
% 0.21/0.54  % (1229)------------------------------
% 0.21/0.55  % (1237)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (1232)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (1233)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (1238)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (1220)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (1226)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (1224)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (1230)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (1231)Refutation not found, incomplete strategy% (1231)------------------------------
% 0.21/0.56  % (1231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1231)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (1231)Memory used [KB]: 1663
% 0.21/0.56  % (1231)Time elapsed: 0.148 s
% 0.21/0.56  % (1231)------------------------------
% 0.21/0.56  % (1231)------------------------------
% 0.21/0.57  % (1240)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.70/0.61  % (1218)Refutation found. Thanks to Tanya!
% 1.70/0.61  % SZS status Theorem for theBenchmark
% 1.70/0.61  % SZS output start Proof for theBenchmark
% 1.70/0.61  fof(f1220,plain,(
% 1.70/0.61    $false),
% 1.70/0.61    inference(trivial_inequality_removal,[],[f1199])).
% 1.70/0.61  fof(f1199,plain,(
% 1.70/0.61    k2_relat_1(sK2) != k2_relat_1(sK2)),
% 1.70/0.61    inference(superposition,[],[f646,f1178])).
% 1.70/0.61  fof(f1178,plain,(
% 1.70/0.61    k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.70/0.61    inference(resolution,[],[f1161,f89])).
% 1.70/0.61  fof(f89,plain,(
% 1.70/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.70/0.61    inference(equality_resolution,[],[f72])).
% 1.70/0.61  fof(f72,plain,(
% 1.70/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.70/0.61    inference(cnf_transformation,[],[f44])).
% 1.70/0.61  fof(f44,plain,(
% 1.70/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.61    inference(flattening,[],[f43])).
% 1.70/0.61  fof(f43,plain,(
% 1.70/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.61    inference(nnf_transformation,[],[f3])).
% 1.70/0.61  fof(f3,axiom,(
% 1.70/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.70/0.61  fof(f1161,plain,(
% 1.70/0.61    ~r1_tarski(sK2,sK2) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.70/0.61    inference(superposition,[],[f1081,f78])).
% 1.70/0.61  fof(f78,plain,(
% 1.70/0.61    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 1.70/0.61    inference(definition_unfolding,[],[f46,f76])).
% 1.70/0.61  fof(f76,plain,(
% 1.70/0.61    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.70/0.61    inference(definition_unfolding,[],[f58,f75])).
% 1.70/0.61  fof(f75,plain,(
% 1.70/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.70/0.61    inference(definition_unfolding,[],[f67,f74])).
% 1.70/0.61  fof(f74,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f6])).
% 1.70/0.61  fof(f6,axiom,(
% 1.70/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.70/0.61  fof(f67,plain,(
% 1.70/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f5])).
% 1.70/0.61  fof(f5,axiom,(
% 1.70/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.70/0.61  fof(f58,plain,(
% 1.70/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f4])).
% 1.70/0.61  fof(f4,axiom,(
% 1.70/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.70/0.61  fof(f46,plain,(
% 1.70/0.61    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 1.70/0.61    inference(cnf_transformation,[],[f22])).
% 1.70/0.61  fof(f22,plain,(
% 1.70/0.61    (k2_relat_1(sK2) != k1_tarski(sK1) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2)),
% 1.70/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21])).
% 1.70/0.61  fof(f21,plain,(
% 1.70/0.61    ? [X0,X1,X2] : ((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2)) => ((k2_relat_1(sK2) != k1_tarski(sK1) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f19,plain,(
% 1.70/0.61    ? [X0,X1,X2] : ((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 1.70/0.61    inference(flattening,[],[f18])).
% 1.70/0.61  fof(f18,plain,(
% 1.70/0.61    ? [X0,X1,X2] : (((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 1.70/0.61    inference(ennf_transformation,[],[f17])).
% 1.70/0.61  fof(f17,negated_conjecture,(
% 1.70/0.61    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2))))),
% 1.70/0.61    inference(negated_conjecture,[],[f16])).
% 1.70/0.61  fof(f16,conjecture,(
% 1.70/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2))))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 1.70/0.61  fof(f1081,plain,(
% 1.70/0.61    ( ! [X4,X3] : (~r1_tarski(k2_enumset1(X3,X3,X3,k4_tarski(X4,sK1)),sK2) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)) )),
% 1.70/0.61    inference(resolution,[],[f1073,f82])).
% 1.70/0.61  fof(f82,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 1.70/0.61    inference(definition_unfolding,[],[f63,f75])).
% 1.70/0.61  fof(f63,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f38])).
% 1.70/0.61  fof(f38,plain,(
% 1.70/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.70/0.61    inference(flattening,[],[f37])).
% 1.70/0.61  fof(f37,plain,(
% 1.70/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.70/0.61    inference(nnf_transformation,[],[f13])).
% 1.70/0.61  fof(f13,axiom,(
% 1.70/0.61    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.70/0.61  fof(f1073,plain,(
% 1.70/0.61    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK1),sK2) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)) )),
% 1.70/0.61    inference(resolution,[],[f1072,f84])).
% 1.70/0.61  fof(f84,plain,(
% 1.70/0.61    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 1.70/0.61    inference(equality_resolution,[],[f49])).
% 1.70/0.61  fof(f49,plain,(
% 1.70/0.61    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.70/0.61    inference(cnf_transformation,[],[f28])).
% 1.70/0.61  fof(f28,plain,(
% 1.70/0.61    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.70/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).
% 1.70/0.61  fof(f25,plain,(
% 1.70/0.61    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f26,plain,(
% 1.70/0.61    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f27,plain,(
% 1.70/0.61    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f24,plain,(
% 1.70/0.61    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.70/0.61    inference(rectify,[],[f23])).
% 1.70/0.61  fof(f23,plain,(
% 1.70/0.61    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.70/0.61    inference(nnf_transformation,[],[f15])).
% 1.70/0.61  fof(f15,axiom,(
% 1.70/0.61    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.70/0.61  fof(f1072,plain,(
% 1.70/0.61    ~r2_hidden(sK1,k2_relat_1(sK2)) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f1070])).
% 1.70/0.61  fof(f1070,plain,(
% 1.70/0.61    k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | ~r2_hidden(sK1,k2_relat_1(sK2)) | ~r2_hidden(sK1,k2_relat_1(sK2))),
% 1.70/0.61    inference(resolution,[],[f1068,f81])).
% 1.70/0.61  fof(f81,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.70/0.61    inference(definition_unfolding,[],[f64,f75])).
% 1.70/0.61  fof(f64,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f38])).
% 1.70/0.61  fof(f1068,plain,(
% 1.70/0.61    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_relat_1(sK2)) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.70/0.61    inference(resolution,[],[f1067,f70])).
% 1.70/0.61  fof(f70,plain,(
% 1.70/0.61    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f42])).
% 1.70/0.61  fof(f42,plain,(
% 1.70/0.61    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.70/0.61    inference(flattening,[],[f41])).
% 1.70/0.61  fof(f41,plain,(
% 1.70/0.61    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.70/0.61    inference(nnf_transformation,[],[f1])).
% 1.70/0.61  fof(f1,axiom,(
% 1.70/0.61    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.70/0.61  fof(f1067,plain,(
% 1.70/0.61    ~r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_relat_1(sK2))),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f1061])).
% 1.70/0.61  fof(f1061,plain,(
% 1.70/0.61    ~r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_relat_1(sK2)) | ~r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_relat_1(sK2))),
% 1.70/0.61    inference(resolution,[],[f1050,f65])).
% 1.70/0.61  fof(f65,plain,(
% 1.70/0.61    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f40])).
% 1.70/0.61  fof(f40,plain,(
% 1.70/0.61    ! [X0,X1] : ((~r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK9(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 1.70/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f20,f39])).
% 1.70/0.61  fof(f39,plain,(
% 1.70/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK9(X0,X1),X1)))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f20,plain,(
% 1.70/0.61    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.70/0.61    inference(ennf_transformation,[],[f2])).
% 1.70/0.61  fof(f2,axiom,(
% 1.70/0.61    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.70/0.61  fof(f1050,plain,(
% 1.70/0.61    ( ! [X2] : (~r2_hidden(sK9(k2_enumset1(sK1,sK1,sK1,sK1),X2),k2_relat_1(sK2)) | ~r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X2)) )),
% 1.70/0.61    inference(resolution,[],[f234,f85])).
% 1.70/0.61  fof(f85,plain,(
% 1.70/0.61    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.70/0.61    inference(equality_resolution,[],[f48])).
% 1.70/0.61  fof(f48,plain,(
% 1.70/0.61    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.70/0.61    inference(cnf_transformation,[],[f28])).
% 1.70/0.61  fof(f234,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK9(k2_enumset1(sK1,sK1,sK1,sK1),X1)),sK2) | ~r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X1)) )),
% 1.70/0.61    inference(superposition,[],[f104,f210])).
% 1.70/0.61  fof(f210,plain,(
% 1.70/0.61    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.70/0.61    inference(superposition,[],[f79,f78])).
% 1.70/0.61  fof(f79,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.70/0.61    inference(definition_unfolding,[],[f57,f75,f76,f75])).
% 1.70/0.61  fof(f57,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.70/0.61    inference(cnf_transformation,[],[f12])).
% 1.70/0.61  fof(f12,axiom,(
% 1.70/0.61    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 1.70/0.61  fof(f104,plain,(
% 1.70/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,sK9(X1,X2)),k2_zfmisc_1(X3,X1)) | ~r2_xboole_0(X1,X2)) )),
% 1.70/0.61    inference(resolution,[],[f60,f66])).
% 1.70/0.61  fof(f66,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f40])).
% 1.70/0.61  fof(f60,plain,(
% 1.70/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.70/0.61    inference(cnf_transformation,[],[f36])).
% 1.70/0.61  fof(f36,plain,(
% 1.70/0.61    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.70/0.61    inference(flattening,[],[f35])).
% 1.70/0.61  fof(f35,plain,(
% 1.70/0.61    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.70/0.61    inference(nnf_transformation,[],[f11])).
% 1.70/0.61  fof(f11,axiom,(
% 1.70/0.61    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.70/0.61  fof(f646,plain,(
% 1.70/0.61    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.70/0.61    inference(trivial_inequality_removal,[],[f637])).
% 1.70/0.61  fof(f637,plain,(
% 1.70/0.61    k1_relat_1(sK2) != k1_relat_1(sK2) | k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.70/0.61    inference(backward_demodulation,[],[f77,f635])).
% 1.70/0.61  fof(f635,plain,(
% 1.70/0.61    k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.70/0.61    inference(resolution,[],[f616,f89])).
% 1.70/0.61  fof(f616,plain,(
% 1.70/0.61    ~r1_tarski(sK2,sK2) | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.70/0.61    inference(superposition,[],[f484,f78])).
% 1.70/0.61  fof(f484,plain,(
% 1.70/0.61    ( ! [X2,X3] : (~r1_tarski(k2_enumset1(X2,X2,X2,k4_tarski(sK0,X3)),sK2) | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)) )),
% 1.70/0.61    inference(resolution,[],[f466,f82])).
% 1.70/0.61  fof(f466,plain,(
% 1.70/0.61    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),sK2) | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)) )),
% 1.70/0.61    inference(resolution,[],[f465,f86])).
% 1.70/0.61  fof(f86,plain,(
% 1.70/0.61    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 1.70/0.61    inference(equality_resolution,[],[f53])).
% 1.70/0.61  fof(f53,plain,(
% 1.70/0.61    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.70/0.61    inference(cnf_transformation,[],[f34])).
% 1.70/0.61  fof(f34,plain,(
% 1.70/0.61    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.70/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f33,f32,f31])).
% 1.70/0.61  fof(f31,plain,(
% 1.70/0.61    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f32,plain,(
% 1.70/0.61    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f33,plain,(
% 1.70/0.61    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f30,plain,(
% 1.70/0.61    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.70/0.61    inference(rectify,[],[f29])).
% 1.70/0.61  fof(f29,plain,(
% 1.70/0.61    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.70/0.61    inference(nnf_transformation,[],[f14])).
% 1.70/0.61  fof(f14,axiom,(
% 1.70/0.61    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.70/0.61  fof(f465,plain,(
% 1.70/0.61    ~r2_hidden(sK0,k1_relat_1(sK2)) | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f463])).
% 1.70/0.61  fof(f463,plain,(
% 1.70/0.61    k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(sK2))),
% 1.70/0.61    inference(resolution,[],[f443,f81])).
% 1.70/0.61  fof(f443,plain,(
% 1.70/0.61    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK2)) | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.70/0.61    inference(resolution,[],[f421,f70])).
% 1.70/0.61  fof(f421,plain,(
% 1.70/0.61    ~r2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK2))),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f415])).
% 1.70/0.61  fof(f415,plain,(
% 1.70/0.61    ~r2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK2)) | ~r2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK2))),
% 1.70/0.61    inference(resolution,[],[f410,f65])).
% 1.70/0.61  fof(f410,plain,(
% 1.70/0.61    ( ! [X0] : (~r2_hidden(sK9(k2_enumset1(sK0,sK0,sK0,sK0),X0),k1_relat_1(sK2)) | ~r2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) )),
% 1.70/0.61    inference(resolution,[],[f214,f87])).
% 1.70/0.61  fof(f87,plain,(
% 1.70/0.61    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 1.70/0.61    inference(equality_resolution,[],[f52])).
% 1.70/0.61  fof(f52,plain,(
% 1.70/0.61    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.70/0.61    inference(cnf_transformation,[],[f34])).
% 1.70/0.61  fof(f214,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK9(k2_enumset1(sK0,sK0,sK0,sK0),X0),X1),sK2) | ~r2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) )),
% 1.70/0.61    inference(superposition,[],[f101,f210])).
% 1.70/0.61  fof(f101,plain,(
% 1.70/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(sK9(X0,X1),X2),k2_zfmisc_1(X0,X3)) | ~r2_xboole_0(X0,X1)) )),
% 1.70/0.61    inference(resolution,[],[f59,f66])).
% 1.70/0.61  fof(f59,plain,(
% 1.70/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.70/0.61    inference(cnf_transformation,[],[f36])).
% 1.70/0.61  fof(f77,plain,(
% 1.70/0.61    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.70/0.61    inference(definition_unfolding,[],[f47,f76,f76])).
% 1.70/0.61  fof(f47,plain,(
% 1.70/0.61    k2_relat_1(sK2) != k1_tarski(sK1) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 1.70/0.61    inference(cnf_transformation,[],[f22])).
% 1.70/0.61  % SZS output end Proof for theBenchmark
% 1.70/0.61  % (1218)------------------------------
% 1.70/0.61  % (1218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.61  % (1218)Termination reason: Refutation
% 1.70/0.61  
% 1.70/0.61  % (1218)Memory used [KB]: 2686
% 1.70/0.61  % (1218)Time elapsed: 0.198 s
% 1.70/0.61  % (1218)------------------------------
% 1.70/0.61  % (1218)------------------------------
% 1.70/0.61  % (1212)Success in time 0.246 s
%------------------------------------------------------------------------------
