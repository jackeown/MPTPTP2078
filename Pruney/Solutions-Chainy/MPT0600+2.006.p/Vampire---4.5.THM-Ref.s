%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 420 expanded)
%              Number of leaves         :   13 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  262 (1554 expanded)
%              Number of equality atoms :   87 ( 370 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(subsumption_resolution,[],[f193,f159])).

fof(f159,plain,(
    r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f131,f84])).

fof(f84,plain,(
    ! [X4,X0] : r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k4_enumset1(X0,X0,X0,X0,X0,X0))
      | r2_hidden(sK1,k11_relat_1(sK2,X0))
      | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ) ),
    inference(superposition,[],[f119,f101])).

fof(f101,plain,(
    ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f37,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f41,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f74])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
        | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
        | r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r2_hidden(X1,k11_relat_1(X2,X0)) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f119,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k9_relat_1(sK2,X0))
      | ~ r2_hidden(sK0,X0)
      | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ) ),
    inference(subsumption_resolution,[],[f117,f108])).

fof(f108,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f105,f38])).

fof(f38,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(k4_tarski(X7,X8),sK2)
      | r2_hidden(X7,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f37,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | r2_hidden(sK1,k9_relat_1(sK2,X0))
      | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ) ),
    inference(resolution,[],[f104,f38])).

fof(f104,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X6),sK2)
      | ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X4,k1_relat_1(sK2))
      | r2_hidden(X6,k9_relat_1(sK2,X5)) ) ),
    inference(resolution,[],[f37,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f193,plain,(
    ~ r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f192,f101])).

fof(f192,plain,(
    ~ r2_hidden(sK1,k9_relat_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(subsumption_resolution,[],[f188,f164])).

fof(f164,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f159,f39])).

fof(f39,plain,
    ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f188,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k9_relat_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f102,f178])).

fof(f178,plain,(
    sK0 = sK3(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f159,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k11_relat_1(sK2,X1))
      | sK3(X0,k4_enumset1(X1,X1,X1,X1,X1,X1),sK2) = X1 ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k11_relat_1(sK2,X1))
      | sK3(X0,k4_enumset1(X1,X1,X1,X1,X1,X1),sK2) = X1
      | sK3(X0,k4_enumset1(X1,X1,X1,X1,X1,X1),sK2) = X1 ) ),
    inference(resolution,[],[f114,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1,k4_enumset1(X0,X0,X0,X0,X0,X0),sK2),k4_enumset1(X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X1,k11_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f103,f101])).

fof(f103,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k9_relat_1(sK2,X3))
      | r2_hidden(sK3(X2,X3,sK2),X3) ) ),
    inference(resolution,[],[f37,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK3(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,sK2),X0),sK2)
      | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f37,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:38:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (21614)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (21625)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (21631)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (21617)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (21607)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (21609)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (21623)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (21614)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (21631)Refutation not found, incomplete strategy% (21631)------------------------------
% 0.22/0.53  % (21631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f193,f159])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f144])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.22/0.54    inference(resolution,[],[f131,f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X4,X0] : (r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X4))) )),
% 0.22/0.54    inference(equality_resolution,[],[f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k4_enumset1(X0,X0,X0,X0,X0,X4) != X2) )),
% 0.22/0.54    inference(equality_resolution,[],[f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 0.22/0.54    inference(definition_unfolding,[],[f52,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f42,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f43,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f56,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.54    inference(rectify,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(sK0,k4_enumset1(X0,X0,X0,X0,X0,X0)) | r2_hidden(sK1,k11_relat_1(sK2,X0)) | r2_hidden(sK1,k11_relat_1(sK2,sK0))) )),
% 0.22/0.54    inference(superposition,[],[f119,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X0] : (k11_relat_1(sK2,X0) = k9_relat_1(sK2,k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f37,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f41,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f40,f74])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    v1_relat_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    (~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & v1_relat_1(sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2)) => ((~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & v1_relat_1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2))) & v1_relat_1(X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r2_hidden(X1,k11_relat_1(X2,X0))) & v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK1,k9_relat_1(sK2,X0)) | ~r2_hidden(sK0,X0) | r2_hidden(sK1,k11_relat_1(sK2,sK0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f117,f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f105,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(sK0,sK1),sK2) | r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X8,X7] : (~r2_hidden(k4_tarski(X7,X8),sK2) | r2_hidden(X7,k1_relat_1(sK2))) )),
% 0.22/0.54    inference(resolution,[],[f37,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK1,k9_relat_1(sK2,X0)) | r2_hidden(sK1,k11_relat_1(sK2,sK0))) )),
% 0.22/0.54    inference(resolution,[],[f104,f38])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X6,X4,X5] : (~r2_hidden(k4_tarski(X4,X6),sK2) | ~r2_hidden(X4,X5) | ~r2_hidden(X4,k1_relat_1(sK2)) | r2_hidden(X6,k9_relat_1(sK2,X5))) )),
% 0.22/0.54    inference(resolution,[],[f37,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(rectify,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.22/0.54    inference(forward_demodulation,[],[f192,f101])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k9_relat_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f188,f164])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f159,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,k9_relat_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.22/0.54    inference(superposition,[],[f102,f178])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    sK0 = sK3(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f159,f163])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k11_relat_1(sK2,X1)) | sK3(X0,k4_enumset1(X1,X1,X1,X1,X1,X1),sK2) = X1) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f160])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k11_relat_1(sK2,X1)) | sK3(X0,k4_enumset1(X1,X1,X1,X1,X1,X1),sK2) = X1 | sK3(X0,k4_enumset1(X1,X1,X1,X1,X1,X1),sK2) = X1) )),
% 0.22/0.54    inference(resolution,[],[f114,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.22/0.54    inference(equality_resolution,[],[f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 0.22/0.54    inference(definition_unfolding,[],[f50,f74])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X1,k4_enumset1(X0,X0,X0,X0,X0,X0),sK2),k4_enumset1(X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X1,k11_relat_1(sK2,X0))) )),
% 0.22/0.54    inference(superposition,[],[f103,f101])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k9_relat_1(sK2,X3)) | r2_hidden(sK3(X2,X3,sK2),X3)) )),
% 0.22/0.54    inference(resolution,[],[f37,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,sK2),X0),sK2) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) )),
% 0.22/0.54    inference(resolution,[],[f37,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (21614)------------------------------
% 0.22/0.54  % (21614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21614)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (21614)Memory used [KB]: 6396
% 0.22/0.54  % (21614)Time elapsed: 0.120 s
% 0.22/0.54  % (21614)------------------------------
% 0.22/0.54  % (21614)------------------------------
% 0.22/0.55  % (21605)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (21631)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21631)Memory used [KB]: 10746
% 0.22/0.55  % (21631)Time elapsed: 0.114 s
% 0.22/0.55  % (21631)------------------------------
% 0.22/0.55  % (21631)------------------------------
% 0.22/0.55  % (21626)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (21602)Success in time 0.178 s
%------------------------------------------------------------------------------
