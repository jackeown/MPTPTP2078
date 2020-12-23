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
% DateTime   : Thu Dec  3 12:51:46 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 948 expanded)
%              Number of leaves         :   30 ( 277 expanded)
%              Depth                    :   23
%              Number of atoms          :  462 (2424 expanded)
%              Number of equality atoms :  131 (1089 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1134,plain,(
    $false ),
    inference(resolution,[],[f1087,f300])).

fof(f300,plain,(
    sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6) ),
    inference(subsumption_resolution,[],[f297,f139])).

fof(f139,plain,(
    sP2(sK6) ),
    inference(subsumption_resolution,[],[f138,f70])).

fof(f70,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5))
    & k1_tarski(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5))
      & k1_tarski(sK5) = k1_relat_1(sK6)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f138,plain,
    ( sP2(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f88,f71])).

fof(f71,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f28,f35,f34,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f297,plain,
    ( sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6)
    | ~ sP2(sK6) ),
    inference(resolution,[],[f296,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | sP0(X0,X1)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f81,f133])).

fof(f133,plain,(
    ! [X0] :
      ( sP1(X0,k2_relat_1(X0))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP0(X3,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK7(X0,X1),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sP0(sK7(X0,X1),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK7(X0,X1),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sP0(sK7(X0,X1),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X2,X0) )
            & ( sP0(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f296,plain,(
    r2_hidden(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),k2_relat_1(sK6)) ),
    inference(subsumption_resolution,[],[f294,f228])).

fof(f228,plain,(
    k1_xboole_0 != k2_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f227,f70])).

fof(f227,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f226,f200])).

fof(f200,plain,(
    r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(resolution,[],[f199,f135])).

fof(f135,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f199,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK6),X0)
      | r2_hidden(sK5,X0) ) ),
    inference(superposition,[],[f128,f123])).

fof(f123,plain,(
    k1_relat_1(sK6) = k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f72,f121])).

fof(f121,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f120])).

fof(f120,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f89,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f100,f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f111,f117])).

fof(f117,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f115,f116])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f111,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f100,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f89,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f74,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f72,plain,(
    k1_tarski(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f109,f120])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f226,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | ~ r2_hidden(sK5,k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(superposition,[],[f90,f215])).

fof(f215,plain,(
    k2_relat_1(sK6) = k11_relat_1(sK6,sK5) ),
    inference(subsumption_resolution,[],[f214,f70])).

fof(f214,plain,
    ( k2_relat_1(sK6) = k11_relat_1(sK6,sK5)
    | ~ v1_relat_1(sK6) ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,
    ( k2_relat_1(sK6) = k11_relat_1(sK6,sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(superposition,[],[f210,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f210,plain,(
    ! [X0] :
      ( k11_relat_1(X0,sK5) = k9_relat_1(X0,k1_relat_1(sK6))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f124,f123])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f78,f121])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f294,plain,
    ( k1_xboole_0 = k2_relat_1(sK6)
    | r2_hidden(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),k2_relat_1(sK6)) ),
    inference(equality_resolution,[],[f251])).

fof(f251,plain,(
    ! [X0] :
      ( k2_relat_1(sK6) != X0
      | k1_xboole_0 = X0
      | r2_hidden(sK10(X0,k1_funct_1(sK6,sK5)),X0) ) ),
    inference(superposition,[],[f122,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f98,f121])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sK10(X0,X1) != X1
        & r2_hidden(sK10(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f31,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK10(X0,X1) != X1
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f122,plain,(
    k2_relat_1(sK6) != k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) ),
    inference(definition_unfolding,[],[f73,f121])).

fof(f73,plain,(
    k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f1087,plain,(
    ! [X8] : ~ sP0(X8,sK6) ),
    inference(subsumption_resolution,[],[f1086,f546])).

fof(f546,plain,(
    ! [X2] :
      ( k1_funct_1(sK6,sK5) = X2
      | ~ sP0(X2,sK6) ) ),
    inference(duplicate_literal_removal,[],[f543])).

fof(f543,plain,(
    ! [X2] :
      ( k1_funct_1(sK6,sK5) = X2
      | ~ sP0(X2,sK6)
      | ~ sP0(X2,sK6) ) ),
    inference(superposition,[],[f86,f521])).

fof(f521,plain,(
    ! [X5] :
      ( sK5 = sK8(X5,sK6)
      | ~ sP0(X5,sK6) ) ),
    inference(resolution,[],[f494,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK8(X0,X1)) = X0
          & r2_hidden(sK8(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK8(X0,X1)) = X0
        & r2_hidden(sK8(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f494,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK6))
      | sK5 = X2 ) ),
    inference(subsumption_resolution,[],[f493,f70])).

fof(f493,plain,(
    ! [X2] :
      ( sK5 = X2
      | ~ r2_hidden(X2,k1_relat_1(sK6))
      | ~ v1_relat_1(sK6) ) ),
    inference(resolution,[],[f473,f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( sP3(k2_relat_1(X0),X0,X1)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f188,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f32,f38,f37])).

fof(f37,plain,(
    ! [X1,X2,X0] :
      ( sP3(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(k4_tarski(X0,X3),X2)
          & r2_hidden(X3,k2_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> sP3(X1,X2,X0) )
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | sP3(k2_relat_1(X0),X0,X1)
      | ~ sP4(X1,X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f101,f75])).

fof(f75,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
      | sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X1,X2))
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r2_hidden(X0,k10_relat_1(X1,X2)) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ~ sP3(X1,X2,X0) )
        & ( sP3(X1,X2,X0)
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f473,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,sK6,X1)
      | sK5 = X1 ) ),
    inference(subsumption_resolution,[],[f468,f70])).

fof(f468,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,sK6,X1)
      | sK5 = X1
      | ~ v1_relat_1(sK6) ) ),
    inference(resolution,[],[f343,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f343,plain,(
    ! [X23,X21,X22,X20] :
      ( ~ r1_tarski(X21,k2_zfmisc_1(k1_relat_1(sK6),X23))
      | ~ sP3(X20,X21,X22)
      | sK5 = X22 ) ),
    inference(resolution,[],[f173,f230])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_relat_1(sK6),X2))
      | sK5 = X0 ) ),
    inference(superposition,[],[f132,f123])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),X3))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f112,f121])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X2,sK11(X0,X1,X2)),X3)
      | ~ sP3(X0,X1,X2)
      | ~ r1_tarski(X1,X3) ) ),
    inference(resolution,[],[f104,f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK11(X0,X1,X2)),X1)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(X3,k2_relat_1(X1)) ) )
      & ( ( r2_hidden(sK11(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(X2,sK11(X0,X1,X2)),X1)
          & r2_hidden(sK11(X0,X1,X2),k2_relat_1(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f63,f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X2,X4),X1)
          & r2_hidden(X4,k2_relat_1(X1)) )
     => ( r2_hidden(sK11(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(X2,sK11(X0,X1,X2)),X1)
        & r2_hidden(sK11(X0,X1,X2),k2_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(X3,k2_relat_1(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X2,X4),X1)
            & r2_hidden(X4,k2_relat_1(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X1,X2,X0] :
      ( ( sP3(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X0,X3),X2)
            | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) )
        | ~ sP3(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK8(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1086,plain,(
    ! [X8] :
      ( k1_funct_1(sK6,sK5) != X8
      | ~ sP0(X8,sK6) ) ),
    inference(subsumption_resolution,[],[f1085,f122])).

fof(f1085,plain,(
    ! [X8] :
      ( k1_funct_1(sK6,sK5) != X8
      | k2_relat_1(sK6) = k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5))
      | ~ sP0(X8,sK6) ) ),
    inference(subsumption_resolution,[],[f1074,f228])).

fof(f1074,plain,(
    ! [X8] :
      ( k1_funct_1(sK6,sK5) != X8
      | k1_xboole_0 = k2_relat_1(sK6)
      | k2_relat_1(sK6) = k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5))
      | ~ sP0(X8,sK6) ) ),
    inference(superposition,[],[f125,f572])).

fof(f572,plain,(
    ! [X0] :
      ( sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = X0
      | ~ sP0(X0,sK6) ) ),
    inference(resolution,[],[f548,f300])).

fof(f548,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,sK6)
      | X0 = X1
      | ~ sP0(X0,sK6) ) ),
    inference(superposition,[],[f546,f546])).

fof(f125,plain,(
    ! [X0,X1] :
      ( sK10(X0,X1) != X1
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f99,f121])).

fof(f99,plain,(
    ! [X0,X1] :
      ( sK10(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:43:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (26985)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (26994)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (27013)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (26992)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (26989)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (26996)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (26990)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (26993)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (26995)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.26/0.54  % (27007)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.54  % (26999)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.26/0.54  % (27002)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.26/0.54  % (27002)Refutation not found, incomplete strategy% (27002)------------------------------
% 1.26/0.54  % (27002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (27002)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (27002)Memory used [KB]: 10618
% 1.26/0.54  % (27002)Time elapsed: 0.123 s
% 1.26/0.54  % (27002)------------------------------
% 1.26/0.54  % (27002)------------------------------
% 1.26/0.54  % (26988)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.54  % (27012)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.26/0.54  % (27014)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.26/0.54  % (27010)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.26/0.54  % (26986)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.55  % (27001)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.26/0.55  % (26987)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.55  % (26991)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.55  % (27004)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.26/0.55  % (27006)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.26/0.55  % (27011)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.26/0.55  % (27008)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.26/0.56  % (27009)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.26/0.56  % (27005)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.26/0.56  % (26997)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.56  % (26998)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.26/0.56  % (27003)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.56  % (27000)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.62  % (27014)Refutation found. Thanks to Tanya!
% 1.50/0.62  % SZS status Theorem for theBenchmark
% 1.50/0.63  % SZS output start Proof for theBenchmark
% 1.50/0.63  fof(f1134,plain,(
% 1.50/0.63    $false),
% 1.50/0.63    inference(resolution,[],[f1087,f300])).
% 1.50/0.63  fof(f300,plain,(
% 1.50/0.63    sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6)),
% 1.50/0.63    inference(subsumption_resolution,[],[f297,f139])).
% 1.50/0.63  fof(f139,plain,(
% 1.50/0.63    sP2(sK6)),
% 1.50/0.63    inference(subsumption_resolution,[],[f138,f70])).
% 1.50/0.63  fof(f70,plain,(
% 1.50/0.63    v1_relat_1(sK6)),
% 1.50/0.63    inference(cnf_transformation,[],[f41])).
% 1.50/0.63  fof(f41,plain,(
% 1.50/0.63    k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5)) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 1.50/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f40])).
% 1.50/0.63  fof(f40,plain,(
% 1.50/0.63    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5)) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 1.50/0.63    introduced(choice_axiom,[])).
% 1.50/0.63  fof(f22,plain,(
% 1.50/0.63    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.50/0.63    inference(flattening,[],[f21])).
% 1.50/0.63  fof(f21,plain,(
% 1.50/0.63    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.50/0.63    inference(ennf_transformation,[],[f20])).
% 1.50/0.63  fof(f20,negated_conjecture,(
% 1.50/0.63    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.50/0.63    inference(negated_conjecture,[],[f19])).
% 1.50/0.63  fof(f19,conjecture,(
% 1.50/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.50/0.63  fof(f138,plain,(
% 1.50/0.63    sP2(sK6) | ~v1_relat_1(sK6)),
% 1.50/0.63    inference(resolution,[],[f88,f71])).
% 1.50/0.63  fof(f71,plain,(
% 1.50/0.63    v1_funct_1(sK6)),
% 1.50/0.63    inference(cnf_transformation,[],[f41])).
% 1.50/0.63  fof(f88,plain,(
% 1.50/0.63    ( ! [X0] : (~v1_funct_1(X0) | sP2(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f36])).
% 1.50/0.63  fof(f36,plain,(
% 1.50/0.63    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(definition_folding,[],[f28,f35,f34,f33])).
% 1.50/0.63  fof(f33,plain,(
% 1.50/0.63    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 1.50/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.50/0.63  fof(f34,plain,(
% 1.50/0.63    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 1.50/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.50/0.63  fof(f35,plain,(
% 1.50/0.63    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 1.50/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.50/0.63  fof(f28,plain,(
% 1.50/0.63    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(flattening,[],[f27])).
% 1.50/0.63  fof(f27,plain,(
% 1.50/0.63    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.63    inference(ennf_transformation,[],[f18])).
% 1.50/0.63  fof(f18,axiom,(
% 1.50/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.50/0.63  fof(f297,plain,(
% 1.50/0.63    sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6) | ~sP2(sK6)),
% 1.50/0.63    inference(resolution,[],[f296,f148])).
% 1.50/0.63  fof(f148,plain,(
% 1.50/0.63    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | sP0(X0,X1) | ~sP2(X1)) )),
% 1.50/0.63    inference(resolution,[],[f81,f133])).
% 1.50/0.63  fof(f133,plain,(
% 1.50/0.63    ( ! [X0] : (sP1(X0,k2_relat_1(X0)) | ~sP2(X0)) )),
% 1.50/0.63    inference(equality_resolution,[],[f79])).
% 1.50/0.63  fof(f79,plain,(
% 1.50/0.63    ( ! [X0,X1] : (sP1(X0,X1) | k2_relat_1(X0) != X1 | ~sP2(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f42])).
% 1.50/0.63  fof(f42,plain,(
% 1.50/0.63    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 1.50/0.63    inference(nnf_transformation,[],[f35])).
% 1.50/0.63  fof(f81,plain,(
% 1.50/0.63    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~r2_hidden(X3,X1) | sP0(X3,X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f46])).
% 1.50/0.63  fof(f46,plain,(
% 1.50/0.63    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (sP0(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.50/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 1.50/0.63  fof(f45,plain,(
% 1.50/0.63    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (sP0(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 1.50/0.63    introduced(choice_axiom,[])).
% 1.50/0.63  fof(f44,plain,(
% 1.50/0.63    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.50/0.63    inference(rectify,[],[f43])).
% 1.50/0.63  fof(f43,plain,(
% 1.50/0.63    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 1.50/0.63    inference(nnf_transformation,[],[f34])).
% 1.50/0.63  fof(f296,plain,(
% 1.50/0.63    r2_hidden(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),k2_relat_1(sK6))),
% 1.50/0.63    inference(subsumption_resolution,[],[f294,f228])).
% 1.50/0.63  fof(f228,plain,(
% 1.50/0.63    k1_xboole_0 != k2_relat_1(sK6)),
% 1.50/0.63    inference(subsumption_resolution,[],[f227,f70])).
% 1.50/0.63  fof(f227,plain,(
% 1.50/0.63    k1_xboole_0 != k2_relat_1(sK6) | ~v1_relat_1(sK6)),
% 1.50/0.63    inference(subsumption_resolution,[],[f226,f200])).
% 1.50/0.63  fof(f200,plain,(
% 1.50/0.63    r2_hidden(sK5,k1_relat_1(sK6))),
% 1.50/0.63    inference(resolution,[],[f199,f135])).
% 1.50/0.63  fof(f135,plain,(
% 1.50/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.63    inference(equality_resolution,[],[f93])).
% 1.50/0.63  fof(f93,plain,(
% 1.50/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.50/0.63    inference(cnf_transformation,[],[f53])).
% 1.50/0.63  fof(f53,plain,(
% 1.50/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.63    inference(flattening,[],[f52])).
% 1.50/0.63  fof(f52,plain,(
% 1.50/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.63    inference(nnf_transformation,[],[f2])).
% 1.50/0.63  fof(f2,axiom,(
% 1.50/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.63  fof(f199,plain,(
% 1.50/0.63    ( ! [X0] : (~r1_tarski(k1_relat_1(sK6),X0) | r2_hidden(sK5,X0)) )),
% 1.50/0.63    inference(superposition,[],[f128,f123])).
% 1.50/0.63  fof(f123,plain,(
% 1.50/0.63    k1_relat_1(sK6) = k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)),
% 1.50/0.63    inference(definition_unfolding,[],[f72,f121])).
% 1.50/0.63  fof(f121,plain,(
% 1.50/0.63    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.50/0.63    inference(definition_unfolding,[],[f74,f120])).
% 1.50/0.63  fof(f120,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.50/0.63    inference(definition_unfolding,[],[f89,f119])).
% 1.50/0.63  fof(f119,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.50/0.63    inference(definition_unfolding,[],[f100,f118])).
% 1.50/0.63  fof(f118,plain,(
% 1.50/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.50/0.63    inference(definition_unfolding,[],[f111,f117])).
% 1.50/0.63  fof(f117,plain,(
% 1.50/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.50/0.63    inference(definition_unfolding,[],[f115,f116])).
% 1.50/0.63  fof(f116,plain,(
% 1.50/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f8])).
% 1.50/0.63  fof(f8,axiom,(
% 1.50/0.63    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.50/0.63  fof(f115,plain,(
% 1.50/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f7])).
% 1.50/0.63  fof(f7,axiom,(
% 1.50/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.50/0.63  fof(f111,plain,(
% 1.50/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f6])).
% 1.50/0.63  fof(f6,axiom,(
% 1.50/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.50/0.63  fof(f100,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f5])).
% 1.50/0.63  fof(f5,axiom,(
% 1.50/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.63  fof(f89,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f4])).
% 1.50/0.63  fof(f4,axiom,(
% 1.50/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.63  fof(f74,plain,(
% 1.50/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f3])).
% 1.50/0.63  fof(f3,axiom,(
% 1.50/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.63  fof(f72,plain,(
% 1.50/0.63    k1_tarski(sK5) = k1_relat_1(sK6)),
% 1.50/0.63    inference(cnf_transformation,[],[f41])).
% 1.50/0.63  fof(f128,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.50/0.63    inference(definition_unfolding,[],[f109,f120])).
% 1.50/0.63  fof(f109,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f67])).
% 1.50/0.63  fof(f67,plain,(
% 1.50/0.63    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.50/0.63    inference(flattening,[],[f66])).
% 1.50/0.63  fof(f66,plain,(
% 1.50/0.63    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.50/0.63    inference(nnf_transformation,[],[f10])).
% 1.50/0.63  fof(f10,axiom,(
% 1.50/0.63    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.50/0.63  fof(f226,plain,(
% 1.50/0.63    k1_xboole_0 != k2_relat_1(sK6) | ~r2_hidden(sK5,k1_relat_1(sK6)) | ~v1_relat_1(sK6)),
% 1.50/0.63    inference(superposition,[],[f90,f215])).
% 1.50/0.63  fof(f215,plain,(
% 1.50/0.63    k2_relat_1(sK6) = k11_relat_1(sK6,sK5)),
% 1.50/0.63    inference(subsumption_resolution,[],[f214,f70])).
% 1.50/0.63  fof(f214,plain,(
% 1.50/0.63    k2_relat_1(sK6) = k11_relat_1(sK6,sK5) | ~v1_relat_1(sK6)),
% 1.50/0.63    inference(duplicate_literal_removal,[],[f211])).
% 1.50/0.63  fof(f211,plain,(
% 1.50/0.63    k2_relat_1(sK6) = k11_relat_1(sK6,sK5) | ~v1_relat_1(sK6) | ~v1_relat_1(sK6)),
% 1.50/0.63    inference(superposition,[],[f210,f76])).
% 1.50/0.63  fof(f76,plain,(
% 1.50/0.63    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f24])).
% 1.50/0.63  fof(f24,plain,(
% 1.50/0.63    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(ennf_transformation,[],[f13])).
% 1.50/0.63  fof(f13,axiom,(
% 1.50/0.63    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.50/0.63  fof(f210,plain,(
% 1.50/0.63    ( ! [X0] : (k11_relat_1(X0,sK5) = k9_relat_1(X0,k1_relat_1(sK6)) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(superposition,[],[f124,f123])).
% 1.50/0.63  fof(f124,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(definition_unfolding,[],[f78,f121])).
% 1.50/0.63  fof(f78,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f26])).
% 1.50/0.63  fof(f26,plain,(
% 1.50/0.63    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(ennf_transformation,[],[f12])).
% 1.50/0.63  fof(f12,axiom,(
% 1.50/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.50/0.63  fof(f90,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f51])).
% 1.50/0.63  fof(f51,plain,(
% 1.50/0.63    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 1.50/0.63    inference(nnf_transformation,[],[f29])).
% 1.50/0.63  fof(f29,plain,(
% 1.50/0.63    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.50/0.63    inference(ennf_transformation,[],[f16])).
% 1.50/0.63  fof(f16,axiom,(
% 1.50/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 1.50/0.63  fof(f294,plain,(
% 1.50/0.63    k1_xboole_0 = k2_relat_1(sK6) | r2_hidden(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),k2_relat_1(sK6))),
% 1.50/0.63    inference(equality_resolution,[],[f251])).
% 1.50/0.63  fof(f251,plain,(
% 1.50/0.63    ( ! [X0] : (k2_relat_1(sK6) != X0 | k1_xboole_0 = X0 | r2_hidden(sK10(X0,k1_funct_1(sK6,sK5)),X0)) )),
% 1.50/0.63    inference(superposition,[],[f122,f126])).
% 1.50/0.63  fof(f126,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK10(X0,X1),X0)) )),
% 1.50/0.63    inference(definition_unfolding,[],[f98,f121])).
% 1.50/0.63  fof(f98,plain,(
% 1.50/0.63    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.50/0.63    inference(cnf_transformation,[],[f59])).
% 1.50/0.63  fof(f59,plain,(
% 1.50/0.63    ! [X0,X1] : ((sK10(X0,X1) != X1 & r2_hidden(sK10(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.50/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f31,f58])).
% 1.50/0.63  fof(f58,plain,(
% 1.50/0.63    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK10(X0,X1) != X1 & r2_hidden(sK10(X0,X1),X0)))),
% 1.50/0.63    introduced(choice_axiom,[])).
% 1.50/0.63  fof(f31,plain,(
% 1.50/0.63    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.50/0.63    inference(ennf_transformation,[],[f11])).
% 1.50/0.63  fof(f11,axiom,(
% 1.50/0.63    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.50/0.63  fof(f122,plain,(
% 1.50/0.63    k2_relat_1(sK6) != k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5))),
% 1.50/0.63    inference(definition_unfolding,[],[f73,f121])).
% 1.50/0.63  fof(f73,plain,(
% 1.50/0.63    k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5))),
% 1.50/0.63    inference(cnf_transformation,[],[f41])).
% 1.50/0.63  fof(f1087,plain,(
% 1.50/0.63    ( ! [X8] : (~sP0(X8,sK6)) )),
% 1.50/0.63    inference(subsumption_resolution,[],[f1086,f546])).
% 1.50/0.63  fof(f546,plain,(
% 1.50/0.63    ( ! [X2] : (k1_funct_1(sK6,sK5) = X2 | ~sP0(X2,sK6)) )),
% 1.50/0.63    inference(duplicate_literal_removal,[],[f543])).
% 1.50/0.63  fof(f543,plain,(
% 1.50/0.63    ( ! [X2] : (k1_funct_1(sK6,sK5) = X2 | ~sP0(X2,sK6) | ~sP0(X2,sK6)) )),
% 1.50/0.63    inference(superposition,[],[f86,f521])).
% 1.50/0.63  fof(f521,plain,(
% 1.50/0.63    ( ! [X5] : (sK5 = sK8(X5,sK6) | ~sP0(X5,sK6)) )),
% 1.50/0.63    inference(resolution,[],[f494,f85])).
% 1.50/0.63  fof(f85,plain,(
% 1.50/0.63    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),k1_relat_1(X1)) | ~sP0(X0,X1)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f50])).
% 1.50/0.63  fof(f50,plain,(
% 1.50/0.63    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK8(X0,X1)) = X0 & r2_hidden(sK8(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 1.50/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f49])).
% 1.50/0.63  fof(f49,plain,(
% 1.50/0.63    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK8(X0,X1)) = X0 & r2_hidden(sK8(X0,X1),k1_relat_1(X1))))),
% 1.50/0.63    introduced(choice_axiom,[])).
% 1.50/0.63  fof(f48,plain,(
% 1.50/0.63    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 1.50/0.63    inference(rectify,[],[f47])).
% 1.50/0.63  fof(f47,plain,(
% 1.50/0.63    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 1.50/0.63    inference(nnf_transformation,[],[f33])).
% 1.50/0.63  fof(f494,plain,(
% 1.50/0.63    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK6)) | sK5 = X2) )),
% 1.50/0.63    inference(subsumption_resolution,[],[f493,f70])).
% 1.50/0.63  fof(f493,plain,(
% 1.50/0.63    ( ! [X2] : (sK5 = X2 | ~r2_hidden(X2,k1_relat_1(sK6)) | ~v1_relat_1(sK6)) )),
% 1.50/0.63    inference(resolution,[],[f473,f189])).
% 1.50/0.63  fof(f189,plain,(
% 1.50/0.63    ( ! [X0,X1] : (sP3(k2_relat_1(X0),X0,X1) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(subsumption_resolution,[],[f188,f107])).
% 1.50/0.63  fof(f107,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (sP4(X0,X2,X1) | ~v1_relat_1(X2)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f39])).
% 1.50/0.63  fof(f39,plain,(
% 1.50/0.63    ! [X0,X1,X2] : (sP4(X0,X2,X1) | ~v1_relat_1(X2))),
% 1.50/0.63    inference(definition_folding,[],[f32,f38,f37])).
% 1.50/0.63  fof(f37,plain,(
% 1.50/0.63    ! [X1,X2,X0] : (sP3(X1,X2,X0) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))))),
% 1.50/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.50/0.63  fof(f38,plain,(
% 1.50/0.63    ! [X0,X2,X1] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> sP3(X1,X2,X0)) | ~sP4(X0,X2,X1))),
% 1.50/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.50/0.63  fof(f32,plain,(
% 1.50/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.50/0.63    inference(ennf_transformation,[],[f14])).
% 1.50/0.63  fof(f14,axiom,(
% 1.50/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 1.50/0.64  fof(f188,plain,(
% 1.50/0.64    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | sP3(k2_relat_1(X0),X0,X1) | ~sP4(X1,X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.50/0.64    inference(superposition,[],[f101,f75])).
% 1.50/0.64  fof(f75,plain,(
% 1.50/0.64    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f23])).
% 1.50/0.64  fof(f23,plain,(
% 1.50/0.64    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.50/0.64    inference(ennf_transformation,[],[f15])).
% 1.50/0.64  fof(f15,axiom,(
% 1.50/0.64    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.50/0.64  fof(f101,plain,(
% 1.50/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X1,X2)) | sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f61])).
% 1.50/0.64  fof(f61,plain,(
% 1.50/0.64    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X1,X2)) | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | ~r2_hidden(X0,k10_relat_1(X1,X2)))) | ~sP4(X0,X1,X2))),
% 1.50/0.64    inference(rectify,[],[f60])).
% 1.50/0.64  fof(f60,plain,(
% 1.50/0.64    ! [X0,X2,X1] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ~sP3(X1,X2,X0)) & (sP3(X1,X2,X0) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~sP4(X0,X2,X1))),
% 1.50/0.64    inference(nnf_transformation,[],[f38])).
% 1.50/0.64  fof(f473,plain,(
% 1.50/0.64    ( ! [X0,X1] : (~sP3(X0,sK6,X1) | sK5 = X1) )),
% 1.50/0.64    inference(subsumption_resolution,[],[f468,f70])).
% 1.50/0.64  fof(f468,plain,(
% 1.50/0.64    ( ! [X0,X1] : (~sP3(X0,sK6,X1) | sK5 = X1 | ~v1_relat_1(sK6)) )),
% 1.50/0.64    inference(resolution,[],[f343,f77])).
% 1.50/0.64  fof(f77,plain,(
% 1.50/0.64    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f25])).
% 1.50/0.64  fof(f25,plain,(
% 1.50/0.64    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.50/0.64    inference(ennf_transformation,[],[f17])).
% 1.50/0.64  fof(f17,axiom,(
% 1.50/0.64    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.50/0.64  fof(f343,plain,(
% 1.50/0.64    ( ! [X23,X21,X22,X20] : (~r1_tarski(X21,k2_zfmisc_1(k1_relat_1(sK6),X23)) | ~sP3(X20,X21,X22) | sK5 = X22) )),
% 1.50/0.64    inference(resolution,[],[f173,f230])).
% 1.50/0.64  fof(f230,plain,(
% 1.50/0.64    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_relat_1(sK6),X2)) | sK5 = X0) )),
% 1.50/0.64    inference(superposition,[],[f132,f123])).
% 1.50/0.64  fof(f132,plain,(
% 1.50/0.64    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),X3)) | X0 = X2) )),
% 1.50/0.64    inference(definition_unfolding,[],[f112,f121])).
% 1.50/0.64  fof(f112,plain,(
% 1.50/0.64    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 1.50/0.64    inference(cnf_transformation,[],[f69])).
% 1.50/0.64  fof(f69,plain,(
% 1.50/0.64    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.50/0.64    inference(flattening,[],[f68])).
% 1.50/0.64  fof(f68,plain,(
% 1.50/0.64    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.50/0.64    inference(nnf_transformation,[],[f9])).
% 1.50/0.64  fof(f9,axiom,(
% 1.50/0.64    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 1.50/0.64  fof(f173,plain,(
% 1.50/0.64    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X2,sK11(X0,X1,X2)),X3) | ~sP3(X0,X1,X2) | ~r1_tarski(X1,X3)) )),
% 1.50/0.64    inference(resolution,[],[f104,f95])).
% 1.50/0.64  fof(f95,plain,(
% 1.50/0.64    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f57])).
% 1.50/0.64  fof(f57,plain,(
% 1.50/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f55,f56])).
% 1.50/0.64  fof(f56,plain,(
% 1.50/0.64    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.50/0.64    introduced(choice_axiom,[])).
% 1.50/0.64  fof(f55,plain,(
% 1.50/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.64    inference(rectify,[],[f54])).
% 1.50/0.64  fof(f54,plain,(
% 1.50/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.64    inference(nnf_transformation,[],[f30])).
% 1.50/0.64  fof(f30,plain,(
% 1.50/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.64    inference(ennf_transformation,[],[f1])).
% 1.50/0.64  fof(f1,axiom,(
% 1.50/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.64  fof(f104,plain,(
% 1.50/0.64    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK11(X0,X1,X2)),X1) | ~sP3(X0,X1,X2)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f65])).
% 1.50/0.64  fof(f65,plain,(
% 1.50/0.64    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,k2_relat_1(X1)))) & ((r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK11(X0,X1,X2)),X1) & r2_hidden(sK11(X0,X1,X2),k2_relat_1(X1))) | ~sP3(X0,X1,X2)))),
% 1.50/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f63,f64])).
% 1.50/0.64  fof(f64,plain,(
% 1.50/0.64    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1) & r2_hidden(X4,k2_relat_1(X1))) => (r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK11(X0,X1,X2)),X1) & r2_hidden(sK11(X0,X1,X2),k2_relat_1(X1))))),
% 1.50/0.64    introduced(choice_axiom,[])).
% 1.50/0.64  fof(f63,plain,(
% 1.50/0.64    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,k2_relat_1(X1)))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1) & r2_hidden(X4,k2_relat_1(X1))) | ~sP3(X0,X1,X2)))),
% 1.50/0.64    inference(rectify,[],[f62])).
% 1.50/0.64  fof(f62,plain,(
% 1.50/0.64    ! [X1,X2,X0] : ((sP3(X1,X2,X0) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~sP3(X1,X2,X0)))),
% 1.50/0.64    inference(nnf_transformation,[],[f37])).
% 1.50/0.64  fof(f86,plain,(
% 1.50/0.64    ( ! [X0,X1] : (k1_funct_1(X1,sK8(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f50])).
% 1.50/0.64  fof(f1086,plain,(
% 1.50/0.64    ( ! [X8] : (k1_funct_1(sK6,sK5) != X8 | ~sP0(X8,sK6)) )),
% 1.50/0.64    inference(subsumption_resolution,[],[f1085,f122])).
% 1.50/0.64  fof(f1085,plain,(
% 1.50/0.64    ( ! [X8] : (k1_funct_1(sK6,sK5) != X8 | k2_relat_1(sK6) = k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) | ~sP0(X8,sK6)) )),
% 1.50/0.64    inference(subsumption_resolution,[],[f1074,f228])).
% 1.50/0.64  fof(f1074,plain,(
% 1.50/0.64    ( ! [X8] : (k1_funct_1(sK6,sK5) != X8 | k1_xboole_0 = k2_relat_1(sK6) | k2_relat_1(sK6) = k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) | ~sP0(X8,sK6)) )),
% 1.50/0.64    inference(superposition,[],[f125,f572])).
% 1.50/0.64  fof(f572,plain,(
% 1.50/0.64    ( ! [X0] : (sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = X0 | ~sP0(X0,sK6)) )),
% 1.50/0.64    inference(resolution,[],[f548,f300])).
% 1.50/0.64  fof(f548,plain,(
% 1.50/0.64    ( ! [X0,X1] : (~sP0(X1,sK6) | X0 = X1 | ~sP0(X0,sK6)) )),
% 1.50/0.64    inference(superposition,[],[f546,f546])).
% 1.50/0.64  fof(f125,plain,(
% 1.50/0.64    ( ! [X0,X1] : (sK10(X0,X1) != X1 | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 1.50/0.64    inference(definition_unfolding,[],[f99,f121])).
% 1.50/0.64  fof(f99,plain,(
% 1.50/0.64    ( ! [X0,X1] : (sK10(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.50/0.64    inference(cnf_transformation,[],[f59])).
% 1.50/0.64  % SZS output end Proof for theBenchmark
% 1.50/0.64  % (27014)------------------------------
% 1.50/0.64  % (27014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.64  % (27014)Termination reason: Refutation
% 1.50/0.64  
% 1.50/0.64  % (27014)Memory used [KB]: 2430
% 1.50/0.64  % (27014)Time elapsed: 0.217 s
% 1.50/0.64  % (27014)------------------------------
% 1.50/0.64  % (27014)------------------------------
% 2.05/0.64  % (26984)Success in time 0.272 s
%------------------------------------------------------------------------------
