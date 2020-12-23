%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:39 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 102 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  267 ( 408 expanded)
%              Number of equality atoms :   41 (  92 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(subsumption_resolution,[],[f226,f58])).

fof(f58,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k1_xboole_0 = k9_relat_1(sK3,sK2)
    & r1_tarski(sK2,k1_relat_1(sK3))
    & k1_xboole_0 != sK2
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK3,sK2)
      & r1_tarski(sK2,k1_relat_1(sK3))
      & k1_xboole_0 != sK2
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f226,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f223,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f19,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f223,plain,(
    ! [X1] : ~ r2_hidden(X1,sK2) ),
    inference(subsumption_resolution,[],[f222,f106])).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK3))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f80,f59])).

fof(f59,plain,(
    r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f222,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f220,f93])).

fof(f93,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f48,f51,f50,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f220,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK3)
      | ~ r2_hidden(X11,sK2) ) ),
    inference(subsumption_resolution,[],[f218,f129])).

fof(f129,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f128,f95])).

fof(f95,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f63,f62])).

fof(f62,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f63,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f128,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f125,f61])).

fof(f61,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f93,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f218,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,sK2)
      | ~ r2_hidden(k4_tarski(X11,X12),sK3)
      | r2_hidden(X12,k1_xboole_0) ) ),
    inference(resolution,[],[f70,f105])).

fof(f105,plain,(
    sP0(sK2,sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f104,f57])).

fof(f57,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f104,plain,
    ( sP0(sK2,sK3,k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f103,f60])).

fof(f60,plain,(
    k1_xboole_0 = k9_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f91,f74])).

fof(f74,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f18,f26,f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> sP0(X1,X0,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | sP0(X1,X0,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ~ sP0(X1,X0,X2) )
          & ( sP0(X1,X0,X2)
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(k4_tarski(X7,X6),X1)
      | r2_hidden(X6,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X1) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r2_hidden(X7,X0)
                  | ~ r2_hidden(k4_tarski(X7,X6),X1) ) )
            & ( ( r2_hidden(sK6(X0,X1,X6),X0)
                & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X1) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X0)
                & r2_hidden(k4_tarski(X5,X3),X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X1) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X0)
              & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) )
     => ( r2_hidden(sK5(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r2_hidden(k4_tarski(X8,X6),X1) )
     => ( r2_hidden(sK6(X0,X1,X6),X0)
        & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X4,X3),X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r2_hidden(X5,X0)
                  & r2_hidden(k4_tarski(X5,X3),X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r2_hidden(X7,X0)
                  | ~ r2_hidden(k4_tarski(X7,X6),X1) ) )
            & ( ? [X8] :
                  ( r2_hidden(X8,X0)
                  & r2_hidden(k4_tarski(X8,X6),X1) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(k4_tarski(X4,X3),X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:36:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (1230077952)
% 0.14/0.37  ipcrm: permission denied for id (1230110722)
% 0.14/0.38  ipcrm: permission denied for id (1230143491)
% 0.14/0.38  ipcrm: permission denied for id (1230209031)
% 0.14/0.39  ipcrm: permission denied for id (1230241806)
% 0.14/0.41  ipcrm: permission denied for id (1230340125)
% 0.22/0.42  ipcrm: permission denied for id (1230405671)
% 0.22/0.44  ipcrm: permission denied for id (1230536763)
% 0.22/0.47  ipcrm: permission denied for id (1230602316)
% 0.22/0.49  ipcrm: permission denied for id (1230766170)
% 0.22/0.50  ipcrm: permission denied for id (1230831716)
% 0.22/0.52  ipcrm: permission denied for id (1230930028)
% 0.22/0.52  ipcrm: permission denied for id (1230962801)
% 0.22/0.53  ipcrm: permission denied for id (1231061108)
% 0.22/0.53  ipcrm: permission denied for id (1231093877)
% 0.22/0.53  ipcrm: permission denied for id (1231126648)
% 0.22/0.54  ipcrm: permission denied for id (1231159419)
% 1.51/0.73  % (9108)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.74  % (9093)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.74  % (9100)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.74  % (9092)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.51/0.75  % (9092)Refutation found. Thanks to Tanya!
% 1.51/0.75  % SZS status Theorem for theBenchmark
% 1.51/0.75  % (9091)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.51/0.75  % (9101)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.75  % (9099)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.51/0.75  % (9109)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.51/0.75  % (9107)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.51/0.76  % (9105)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.77  % SZS output start Proof for theBenchmark
% 1.51/0.77  fof(f231,plain,(
% 1.51/0.77    $false),
% 1.51/0.77    inference(subsumption_resolution,[],[f226,f58])).
% 1.51/0.77  fof(f58,plain,(
% 1.51/0.77    k1_xboole_0 != sK2),
% 1.51/0.77    inference(cnf_transformation,[],[f29])).
% 1.51/0.77  fof(f29,plain,(
% 1.51/0.77    k1_xboole_0 = k9_relat_1(sK3,sK2) & r1_tarski(sK2,k1_relat_1(sK3)) & k1_xboole_0 != sK2 & v1_relat_1(sK3)),
% 1.51/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f28])).
% 1.51/0.77  fof(f28,plain,(
% 1.51/0.77    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k9_relat_1(sK3,sK2) & r1_tarski(sK2,k1_relat_1(sK3)) & k1_xboole_0 != sK2 & v1_relat_1(sK3))),
% 1.51/0.77    introduced(choice_axiom,[])).
% 1.51/0.77  fof(f16,plain,(
% 1.51/0.77    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 1.51/0.77    inference(flattening,[],[f15])).
% 1.51/0.77  fof(f15,plain,(
% 1.51/0.77    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 1.51/0.77    inference(ennf_transformation,[],[f14])).
% 1.51/0.77  fof(f14,negated_conjecture,(
% 1.51/0.77    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.51/0.77    inference(negated_conjecture,[],[f13])).
% 1.51/0.77  fof(f13,conjecture,(
% 1.51/0.77    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.51/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 1.51/0.77  fof(f226,plain,(
% 1.51/0.77    k1_xboole_0 = sK2),
% 1.51/0.77    inference(resolution,[],[f223,f77])).
% 1.51/0.77  fof(f77,plain,(
% 1.51/0.77    ( ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 1.51/0.77    inference(cnf_transformation,[],[f42])).
% 1.51/0.77  fof(f42,plain,(
% 1.51/0.77    ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0)),
% 1.51/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f19,f41])).
% 1.51/0.77  fof(f41,plain,(
% 1.51/0.77    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 1.51/0.77    introduced(choice_axiom,[])).
% 1.51/0.77  fof(f19,plain,(
% 1.51/0.77    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.51/0.77    inference(ennf_transformation,[],[f4])).
% 1.51/0.77  fof(f4,axiom,(
% 1.51/0.77    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.51/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.51/0.77  fof(f223,plain,(
% 1.51/0.77    ( ! [X1] : (~r2_hidden(X1,sK2)) )),
% 1.51/0.77    inference(subsumption_resolution,[],[f222,f106])).
% 1.51/0.77  fof(f106,plain,(
% 1.51/0.77    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK3)) | ~r2_hidden(X0,sK2)) )),
% 1.51/0.77    inference(resolution,[],[f80,f59])).
% 1.51/0.77  fof(f59,plain,(
% 1.51/0.77    r1_tarski(sK2,k1_relat_1(sK3))),
% 1.51/0.77    inference(cnf_transformation,[],[f29])).
% 1.51/0.77  fof(f80,plain,(
% 1.51/0.77    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.51/0.77    inference(cnf_transformation,[],[f46])).
% 1.51/0.77  fof(f46,plain,(
% 1.51/0.77    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).
% 1.51/0.77  fof(f45,plain,(
% 1.51/0.77    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.51/0.77    introduced(choice_axiom,[])).
% 1.51/0.77  fof(f44,plain,(
% 1.51/0.77    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.77    inference(rectify,[],[f43])).
% 1.51/0.77  fof(f43,plain,(
% 1.51/0.77    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.77    inference(nnf_transformation,[],[f23])).
% 1.51/0.77  fof(f23,plain,(
% 1.51/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.77    inference(ennf_transformation,[],[f2])).
% 1.51/0.77  fof(f2,axiom,(
% 1.51/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.77  fof(f222,plain,(
% 1.51/0.77    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,k1_relat_1(sK3))) )),
% 1.51/0.77    inference(resolution,[],[f220,f93])).
% 1.51/0.77  fof(f93,plain,(
% 1.51/0.77    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 1.51/0.77    inference(equality_resolution,[],[f83])).
% 1.51/0.77  fof(f83,plain,(
% 1.51/0.77    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.51/0.77    inference(cnf_transformation,[],[f52])).
% 1.51/0.77  fof(f52,plain,(
% 1.51/0.77    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.51/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f48,f51,f50,f49])).
% 1.51/0.77  fof(f49,plain,(
% 1.51/0.77    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 1.51/0.77    introduced(choice_axiom,[])).
% 1.51/0.77  fof(f50,plain,(
% 1.51/0.77    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0))),
% 1.51/0.77    introduced(choice_axiom,[])).
% 1.51/0.77  fof(f51,plain,(
% 1.51/0.77    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0))),
% 1.51/0.77    introduced(choice_axiom,[])).
% 1.51/0.77  fof(f48,plain,(
% 1.51/0.77    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.51/0.77    inference(rectify,[],[f47])).
% 1.51/0.77  fof(f47,plain,(
% 1.51/0.77    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.51/0.77    inference(nnf_transformation,[],[f7])).
% 1.51/0.77  fof(f7,axiom,(
% 1.51/0.77    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.51/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.51/0.77  fof(f220,plain,(
% 1.51/0.77    ( ! [X12,X11] : (~r2_hidden(k4_tarski(X11,X12),sK3) | ~r2_hidden(X11,sK2)) )),
% 1.51/0.77    inference(subsumption_resolution,[],[f218,f129])).
% 1.51/0.77  fof(f129,plain,(
% 1.51/0.77    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.51/0.77    inference(forward_demodulation,[],[f128,f95])).
% 1.51/0.77  fof(f95,plain,(
% 1.51/0.77    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.51/0.77    inference(superposition,[],[f63,f62])).
% 1.51/0.77  fof(f62,plain,(
% 1.51/0.77    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.51/0.77    inference(cnf_transformation,[],[f11])).
% 1.51/0.77  fof(f11,axiom,(
% 1.51/0.77    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.51/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.51/0.77  fof(f63,plain,(
% 1.51/0.77    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.51/0.77    inference(cnf_transformation,[],[f10])).
% 1.51/0.77  fof(f10,axiom,(
% 1.51/0.77    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.51/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.51/0.77  fof(f128,plain,(
% 1.51/0.77    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 1.51/0.77    inference(resolution,[],[f125,f61])).
% 1.51/0.77  fof(f61,plain,(
% 1.51/0.77    v1_xboole_0(k1_xboole_0)),
% 1.51/0.77    inference(cnf_transformation,[],[f3])).
% 1.51/0.77  fof(f3,axiom,(
% 1.51/0.77    v1_xboole_0(k1_xboole_0)),
% 1.51/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.51/0.77  fof(f125,plain,(
% 1.51/0.77    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 1.51/0.77    inference(resolution,[],[f93,f75])).
% 1.51/0.77  fof(f75,plain,(
% 1.51/0.77    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.51/0.77    inference(cnf_transformation,[],[f40])).
% 1.51/0.77  fof(f40,plain,(
% 1.51/0.77    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).
% 1.51/0.77  fof(f39,plain,(
% 1.51/0.77    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 1.51/0.77    introduced(choice_axiom,[])).
% 1.51/0.77  fof(f38,plain,(
% 1.51/0.77    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.77    inference(rectify,[],[f37])).
% 1.51/0.77  fof(f37,plain,(
% 1.51/0.77    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.77    inference(nnf_transformation,[],[f1])).
% 1.51/0.77  fof(f1,axiom,(
% 1.51/0.77    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.51/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.51/0.77  fof(f218,plain,(
% 1.51/0.77    ( ! [X12,X11] : (~r2_hidden(X11,sK2) | ~r2_hidden(k4_tarski(X11,X12),sK3) | r2_hidden(X12,k1_xboole_0)) )),
% 1.51/0.77    inference(resolution,[],[f70,f105])).
% 1.51/0.77  fof(f105,plain,(
% 1.51/0.77    sP0(sK2,sK3,k1_xboole_0)),
% 1.51/0.77    inference(subsumption_resolution,[],[f104,f57])).
% 1.51/0.77  fof(f57,plain,(
% 1.51/0.77    v1_relat_1(sK3)),
% 1.51/0.77    inference(cnf_transformation,[],[f29])).
% 1.51/0.77  fof(f104,plain,(
% 1.51/0.77    sP0(sK2,sK3,k1_xboole_0) | ~v1_relat_1(sK3)),
% 1.51/0.77    inference(superposition,[],[f103,f60])).
% 1.51/0.77  fof(f60,plain,(
% 1.51/0.77    k1_xboole_0 = k9_relat_1(sK3,sK2)),
% 1.51/0.77    inference(cnf_transformation,[],[f29])).
% 1.51/0.77  fof(f103,plain,(
% 1.51/0.77    ( ! [X0,X1] : (sP0(X0,X1,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.51/0.77    inference(resolution,[],[f91,f74])).
% 1.51/0.77  fof(f74,plain,(
% 1.51/0.77    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.77    inference(cnf_transformation,[],[f27])).
% 1.51/0.77  fof(f27,plain,(
% 1.51/0.77    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 1.51/0.77    inference(definition_folding,[],[f18,f26,f25])).
% 1.51/0.77  fof(f25,plain,(
% 1.51/0.77    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0))))),
% 1.51/0.77    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.51/0.77  fof(f26,plain,(
% 1.51/0.77    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X0))),
% 1.51/0.77    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.51/0.77  fof(f18,plain,(
% 1.51/0.77    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 1.51/0.77    inference(ennf_transformation,[],[f6])).
% 1.51/0.77  fof(f6,axiom,(
% 1.51/0.77    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 1.51/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 1.51/0.77  fof(f91,plain,(
% 1.51/0.77    ( ! [X0,X1] : (~sP1(X0) | sP0(X1,X0,k9_relat_1(X0,X1))) )),
% 1.51/0.77    inference(equality_resolution,[],[f66])).
% 1.51/0.77  fof(f66,plain,(
% 1.51/0.77    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k9_relat_1(X0,X1) != X2 | ~sP1(X0)) )),
% 1.51/0.77    inference(cnf_transformation,[],[f30])).
% 1.51/0.77  fof(f30,plain,(
% 1.51/0.77    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k9_relat_1(X0,X1) != X2)) | ~sP1(X0))),
% 1.51/0.77    inference(nnf_transformation,[],[f26])).
% 1.51/0.77  fof(f70,plain,(
% 1.51/0.77    ( ! [X6,X2,X0,X7,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X7,X0) | ~r2_hidden(k4_tarski(X7,X6),X1) | r2_hidden(X6,X2)) )),
% 1.51/0.77    inference(cnf_transformation,[],[f36])).
% 1.51/0.77  fof(f36,plain,(
% 1.51/0.77    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X0) | ~r2_hidden(k4_tarski(X7,X6),X1))) & ((r2_hidden(sK6(X0,X1,X6),X0) & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X1)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 1.51/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).
% 1.51/0.77  fof(f33,plain,(
% 1.51/0.77    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X0) & r2_hidden(k4_tarski(X5,X3),X1)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X0) & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.51/0.77    introduced(choice_axiom,[])).
% 1.51/0.77  fof(f34,plain,(
% 1.51/0.77    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X0) & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)) => (r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)))),
% 1.51/0.77    introduced(choice_axiom,[])).
% 1.51/0.77  fof(f35,plain,(
% 1.51/0.77    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X0) & r2_hidden(k4_tarski(X8,X6),X1)) => (r2_hidden(sK6(X0,X1,X6),X0) & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X1)))),
% 1.51/0.77    introduced(choice_axiom,[])).
% 1.51/0.77  fof(f32,plain,(
% 1.51/0.77    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X0) & r2_hidden(k4_tarski(X5,X3),X1)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X0) | ~r2_hidden(k4_tarski(X7,X6),X1))) & (? [X8] : (r2_hidden(X8,X0) & r2_hidden(k4_tarski(X8,X6),X1)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 1.51/0.77    inference(rectify,[],[f31])).
% 1.51/0.77  fof(f31,plain,(
% 1.51/0.77    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.51/0.77    inference(nnf_transformation,[],[f25])).
% 1.51/0.77  % SZS output end Proof for theBenchmark
% 1.51/0.77  % (9092)------------------------------
% 1.51/0.77  % (9092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.77  % (9092)Termination reason: Refutation
% 1.51/0.77  
% 1.51/0.77  % (9092)Memory used [KB]: 6396
% 1.51/0.77  % (9092)Time elapsed: 0.131 s
% 1.51/0.77  % (9092)------------------------------
% 1.51/0.77  % (9092)------------------------------
% 1.51/0.77  % (8915)Success in time 0.4 s
%------------------------------------------------------------------------------
