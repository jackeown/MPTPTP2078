%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 259 expanded)
%              Number of leaves         :   16 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  283 ( 945 expanded)
%              Number of equality atoms :  127 ( 452 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(subsumption_resolution,[],[f172,f46])).

fof(f46,plain,(
    k2_relat_1(sK3) != k1_tarski(k1_funct_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k2_relat_1(sK3) != k1_tarski(k1_funct_1(sK3,sK2))
    & k1_tarski(sK2) = k1_relat_1(sK3)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK3) != k1_tarski(k1_funct_1(sK3,sK2))
      & k1_tarski(sK2) = k1_relat_1(sK3)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f172,plain,(
    k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,sK2)) ),
    inference(equality_resolution,[],[f170])).

fof(f170,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK2) != X0
      | k1_tarski(X0) = k2_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f169,f137])).

fof(f137,plain,(
    k1_xboole_0 != k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f89,f133])).

fof(f133,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f132,f74])).

fof(f74,plain,(
    ! [X4,X2,X3,X1] : sP0(X1,X1,X2,X3,X4) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( ( sP0(X5,X3,X2,X1,X0)
        | ( X3 != X5
          & X2 != X5
          & X1 != X5
          & X0 != X5 ) )
      & ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5
        | ~ sP0(X5,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( ( sP0(X5,X3,X2,X1,X0)
        | ( X3 != X5
          & X2 != X5
          & X1 != X5
          & X0 != X5 ) )
      & ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5
        | ~ sP0(X5,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( sP0(X5,X3,X2,X1,X0)
    <=> ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f132,plain,(
    ! [X12,X13] :
      ( ~ sP0(X12,X13,X13,X13,X13)
      | r2_hidden(X12,k1_tarski(X13)) ) ),
    inference(resolution,[],[f63,f86])).

fof(f86,plain,(
    ! [X0] : sP1(X0,X0,X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f85,f47])).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f85,plain,(
    ! [X0,X1] : sP1(X0,X0,X0,X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f84,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f84,plain,(
    ! [X2,X0,X1] : sP1(X0,X0,X1,X2,k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f78,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : sP1(X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP1(X0,X1,X2,X3,X4) )
      & ( sP1(X0,X1,X2,X3,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP1(X0,X1,X2,X3,X4) ) ),
    inference(definition_folding,[],[f23,f25,f24])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP1(X0,X1,X2,X3,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> sP0(X5,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | ~ sP0(X6,X3,X2,X1,X0)
      | r2_hidden(X6,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
          & ( sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ~ sP0(X6,X3,X2,X1,X0) )
            & ( sP0(X6,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ sP0(X5,X3,X2,X1,X0)
            | ~ r2_hidden(X5,X4) )
          & ( sP0(X5,X3,X2,X1,X0)
            | r2_hidden(X5,X4) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
        & ( sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ~ sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) )
            & ( sP0(X5,X3,X2,X1,X0)
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ~ sP0(X6,X3,X2,X1,X0) )
            & ( sP0(X6,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ~ sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) )
            & ( sP0(X5,X3,X2,X1,X0)
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ~ sP0(X5,X3,X2,X1,X0) )
            & ( sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f89,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f88,f45])).

fof(f45,plain,(
    k1_tarski(sK2) = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f87,f43])).

fof(f43,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f51,f82])).

fof(f82,plain,(
    k2_relat_1(sK3) = k11_relat_1(sK3,sK2) ),
    inference(superposition,[],[f81,f80])).

fof(f80,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f79,f45])).

fof(f79,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f81,plain,(
    ! [X0] : k11_relat_1(sK3,X0) = k9_relat_1(sK3,k1_tarski(X0)) ),
    inference(resolution,[],[f49,f43])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f169,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK2) != X0
      | k1_xboole_0 = k2_relat_1(sK3)
      | k1_tarski(X0) = k2_relat_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK2) != X0
      | k1_xboole_0 = k2_relat_1(sK3)
      | k1_tarski(X0) = k2_relat_1(sK3)
      | k1_tarski(X0) = k2_relat_1(sK3) ) ),
    inference(superposition,[],[f54,f138])).

fof(f138,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK2) = sK4(k2_relat_1(sK3),X0)
      | k1_tarski(X0) = k2_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f128,f137])).

fof(f128,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK2) = sK4(k2_relat_1(sK3),X0)
      | k1_xboole_0 = k2_relat_1(sK3)
      | k1_tarski(X0) = k2_relat_1(sK3) ) ),
    inference(resolution,[],[f127,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sK4(X0,X1) != X1
        & r2_hidden(sK4(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK4(X0,X1) != X1
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | k1_funct_1(sK3,sK2) = X0 ) ),
    inference(superposition,[],[f121,f82])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK3,X0))
      | k1_funct_1(sK3,X0) = X1 ) ),
    inference(resolution,[],[f120,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),sK3)
      | ~ r2_hidden(X0,k11_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f57,f43])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | k1_funct_1(sK3,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | k1_funct_1(sK3,X0) = X1
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f59,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:37:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (32694)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.46  % (32702)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.47  % (32702)Refutation not found, incomplete strategy% (32702)------------------------------
% 0.20/0.47  % (32702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (32694)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (32702)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (32702)Memory used [KB]: 6396
% 0.20/0.47  % (32702)Time elapsed: 0.060 s
% 0.20/0.47  % (32702)------------------------------
% 0.20/0.47  % (32702)------------------------------
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f172,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    k2_relat_1(sK3) != k1_tarski(k1_funct_1(sK3,sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    k2_relat_1(sK3) != k1_tarski(k1_funct_1(sK3,sK2)) & k1_tarski(sK2) = k1_relat_1(sK3) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK3) != k1_tarski(k1_funct_1(sK3,sK2)) & k1_tarski(sK2) = k1_relat_1(sK3) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.48    inference(negated_conjecture,[],[f12])).
% 0.20/0.48  fof(f12,conjecture,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,sK2))),
% 0.20/0.48    inference(equality_resolution,[],[f170])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK3,sK2) != X0 | k1_tarski(X0) = k2_relat_1(sK3)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f169,f137])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    k1_xboole_0 != k2_relat_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f89,f133])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.20/0.48    inference(resolution,[],[f132,f74])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ( ! [X4,X2,X3,X1] : (sP0(X1,X1,X2,X3,X4)) )),
% 0.20/0.48    inference(equality_resolution,[],[f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | X0 != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | ~sP0(X0,X1,X2,X3,X4)))),
% 0.20/0.48    inference(rectify,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X5,X3,X2,X1,X0] : ((sP0(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~sP0(X5,X3,X2,X1,X0)))),
% 0.20/0.48    inference(flattening,[],[f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ! [X5,X3,X2,X1,X0] : ((sP0(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~sP0(X5,X3,X2,X1,X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X5,X3,X2,X1,X0] : (sP0(X5,X3,X2,X1,X0) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ( ! [X12,X13] : (~sP0(X12,X13,X13,X13,X13) | r2_hidden(X12,k1_tarski(X13))) )),
% 0.20/0.48    inference(resolution,[],[f63,f86])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ( ! [X0] : (sP1(X0,X0,X0,X0,k1_tarski(X0))) )),
% 0.20/0.48    inference(superposition,[],[f85,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP1(X0,X0,X0,X1,k2_tarski(X0,X1))) )),
% 0.20/0.48    inference(superposition,[],[f84,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP1(X0,X0,X1,X2,k1_enumset1(X0,X1,X2))) )),
% 0.20/0.48    inference(superposition,[],[f78,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3))) )),
% 0.20/0.48    inference(equality_resolution,[],[f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.20/0.48    inference(cnf_transformation,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP1(X0,X1,X2,X3,X4)) & (sP1(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.20/0.48    inference(nnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP1(X0,X1,X2,X3,X4))),
% 0.20/0.48    inference(definition_folding,[],[f23,f25,f24])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (sP1(X0,X1,X2,X3,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> sP0(X5,X3,X2,X1,X0)))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3,X4) | ~sP0(X6,X3,X2,X1,X0) | r2_hidden(X6,X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ((~sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP0(X6,X3,X2,X1,X0)) & (sP0(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X4,X3,X2,X1,X0] : (? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4))) => ((~sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4),X4))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP0(X6,X3,X2,X1,X0)) & (sP0(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.20/0.48    inference(rectify,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | ~sP0(X5,X3,X2,X1,X0)) & (sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.20/0.48    inference(nnf_transformation,[],[f25])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ~r2_hidden(sK2,k1_tarski(sK2)) | k1_xboole_0 != k2_relat_1(sK3)),
% 0.20/0.48    inference(forward_demodulation,[],[f88,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    k1_tarski(sK2) = k1_relat_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    k1_xboole_0 != k2_relat_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3))),
% 0.20/0.48    inference(subsumption_resolution,[],[f87,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    v1_relat_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    k1_xboole_0 != k2_relat_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.20/0.48    inference(superposition,[],[f51,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    k2_relat_1(sK3) = k11_relat_1(sK3,sK2)),
% 0.20/0.48    inference(superposition,[],[f81,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK2))),
% 0.20/0.48    inference(forward_demodulation,[],[f79,f45])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3))),
% 0.20/0.48    inference(resolution,[],[f48,f43])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ( ! [X0] : (k11_relat_1(sK3,X0) = k9_relat_1(sK3,k1_tarski(X0))) )),
% 0.20/0.48    inference(resolution,[],[f49,f43])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK3,sK2) != X0 | k1_xboole_0 = k2_relat_1(sK3) | k1_tarski(X0) = k2_relat_1(sK3)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f166])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK3,sK2) != X0 | k1_xboole_0 = k2_relat_1(sK3) | k1_tarski(X0) = k2_relat_1(sK3) | k1_tarski(X0) = k2_relat_1(sK3)) )),
% 0.20/0.48    inference(superposition,[],[f54,f138])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK3,sK2) = sK4(k2_relat_1(sK3),X0) | k1_tarski(X0) = k2_relat_1(sK3)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f128,f137])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK3,sK2) = sK4(k2_relat_1(sK3),X0) | k1_xboole_0 = k2_relat_1(sK3) | k1_tarski(X0) = k2_relat_1(sK3)) )),
% 0.20/0.48    inference(resolution,[],[f127,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1] : ((sK4(X0,X1) != X1 & r2_hidden(sK4(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK4(X0,X1) != X1 & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK2) = X0) )),
% 0.20/0.48    inference(superposition,[],[f121,f82])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK3,X0)) | k1_funct_1(sK3,X0) = X1) )),
% 0.20/0.48    inference(resolution,[],[f120,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),sK3) | ~r2_hidden(X0,k11_relat_1(sK3,X1))) )),
% 0.20/0.48    inference(resolution,[],[f57,f43])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f119,f43])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1 | ~v1_relat_1(sK3)) )),
% 0.20/0.48    inference(resolution,[],[f59,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    v1_funct_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sK4(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (32694)------------------------------
% 0.20/0.48  % (32694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (32694)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (32694)Memory used [KB]: 6396
% 0.20/0.48  % (32694)Time elapsed: 0.060 s
% 0.20/0.48  % (32694)------------------------------
% 0.20/0.48  % (32694)------------------------------
% 0.20/0.48  % (32686)Success in time 0.123 s
%------------------------------------------------------------------------------
