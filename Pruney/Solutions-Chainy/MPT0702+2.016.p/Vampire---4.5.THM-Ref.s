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
% DateTime   : Thu Dec  3 12:54:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 331 expanded)
%              Number of leaves         :   11 (  83 expanded)
%              Depth                    :   30
%              Number of atoms          :  323 (1715 expanded)
%              Number of equality atoms :   16 (  42 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(subsumption_resolution,[],[f280,f41])).

fof(f41,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(sK2,sK3)
    & v2_funct_1(sK4)
    & r1_tarski(sK2,k1_relat_1(sK4))
    & r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK2,sK3)
      & v2_funct_1(sK4)
      & r1_tarski(sK2,k1_relat_1(sK4))
      & r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f280,plain,(
    r1_tarski(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f277])).

fof(f277,plain,
    ( r1_tarski(sK2,sK3)
    | r1_tarski(sK2,sK3) ),
    inference(resolution,[],[f273,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f273,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK2,X0),sK3)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f272,f172])).

fof(f172,plain,(
    ! [X14,X15,X13] :
      ( ~ r1_tarski(X13,k10_relat_1(sK4,k9_relat_1(sK4,X15)))
      | r2_hidden(sK6(X13,X14),X15)
      | r1_tarski(X13,X14) ) ),
    inference(resolution,[],[f74,f82])).

fof(f82,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) ),
    inference(subsumption_resolution,[],[f81,f36])).

fof(f36,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f80,f37])).

fof(f37,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f74,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r1_tarski(X8,X10)
      | r1_tarski(X7,X9)
      | r2_hidden(sK6(X7,X9),X10)
      | ~ r1_tarski(X7,X8) ) ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f57,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f272,plain,(
    r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK3))) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,
    ( r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK3)))
    | r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK3))) ),
    inference(resolution,[],[f267,f59])).

fof(f267,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK2,X0),k10_relat_1(sK4,k9_relat_1(sK4,sK3)))
      | r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f266,f36])).

fof(f266,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | r2_hidden(sK6(sK2,X0),k10_relat_1(sK4,k9_relat_1(sK4,sK3)))
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f265,f37])).

fof(f265,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | r2_hidden(sK6(sK2,X0),k10_relat_1(sK4,k9_relat_1(sK4,sK3)))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f261,f50])).

fof(f50,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f12,f20,f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
            & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> sP0(X1,X0,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f261,plain,(
    ! [X0] :
      ( ~ sP1(sK4)
      | r1_tarski(sK2,X0)
      | r2_hidden(sK6(sK2,X0),k10_relat_1(sK4,k9_relat_1(sK4,sK3))) ) ),
    inference(resolution,[],[f256,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0,k10_relat_1(X0,X1))
      | ~ sP1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ~ sP0(X1,X0,X2) )
          & ( sP0(X1,X0,X2)
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f256,plain,(
    ! [X6,X5] :
      ( ~ sP0(k9_relat_1(sK4,sK3),sK4,X6)
      | r2_hidden(sK6(sK2,X5),X6)
      | r1_tarski(sK2,X5) ) ),
    inference(subsumption_resolution,[],[f255,f131])).

fof(f131,plain,(
    ! [X3] :
      ( r2_hidden(sK6(sK2,X3),k1_relat_1(sK4))
      | r1_tarski(sK2,X3) ) ),
    inference(resolution,[],[f71,f96])).

fof(f96,plain,(
    sP0(k9_relat_1(sK4,sK2),sK4,sK2) ),
    inference(subsumption_resolution,[],[f95,f36])).

fof(f95,plain,
    ( sP0(k9_relat_1(sK4,sK2),sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f94,f37])).

fof(f94,plain,
    ( sP0(k9_relat_1(sK4,sK2),sK4,sK2)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f92,f50])).

fof(f92,plain,
    ( ~ sP1(sK4)
    | sP0(k9_relat_1(sK4,sK2),sK4,sK2) ),
    inference(superposition,[],[f60,f88])).

fof(f88,plain,(
    sK2 = k10_relat_1(sK4,k9_relat_1(sK4,sK2)) ),
    inference(resolution,[],[f83,f39])).

fof(f39,plain,(
    r1_tarski(sK2,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK4))
      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f79,f82])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK4))
      | ~ r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0)
      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ) ),
    inference(resolution,[],[f78,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f78,plain,(
    ! [X0] :
      ( r1_tarski(X0,k10_relat_1(sK4,k9_relat_1(sK4,X0)))
      | ~ r1_tarski(X0,k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f52,f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X2,X0)
      | r2_hidden(sK6(X0,X1),k1_relat_1(X2))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f44,f58])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1))
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0)
              & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k1_funct_1(X1,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X1,X4),X0)
                & r2_hidden(X4,k1_relat_1(X1)) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X1,X3),X0)
            | ~ r2_hidden(X3,k1_relat_1(X1))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X1,X3),X0)
              & r2_hidden(X3,k1_relat_1(X1)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1))
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k1_funct_1(X1,X3),X0)
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k1_funct_1(X1,X3),X0)
                & r2_hidden(X3,k1_relat_1(X1)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k1_funct_1(X1,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X1,X4),X0)
                & r2_hidden(X4,k1_relat_1(X1)) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
              | ~ r2_hidden(X3,k1_relat_1(X0))
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(k1_funct_1(X0,X3),X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
              | ~ r2_hidden(X3,k1_relat_1(X0))
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(k1_funct_1(X0,X3),X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f255,plain,(
    ! [X6,X5] :
      ( r1_tarski(sK2,X5)
      | r2_hidden(sK6(sK2,X5),X6)
      | ~ r2_hidden(sK6(sK2,X5),k1_relat_1(sK4))
      | ~ sP0(k9_relat_1(sK4,sK3),sK4,X6) ) ),
    inference(resolution,[],[f250,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X1,X4),X0)
      | r2_hidden(X4,X2)
      | ~ r2_hidden(X4,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f250,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK4,sK6(sK2,X0)),k9_relat_1(sK4,sK3))
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f161,f38])).

fof(f38,plain,(
    r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK4,sK2),X1)
      | r2_hidden(k1_funct_1(sK4,sK6(sK2,X0)),X1)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f107,f58])).

fof(f107,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(k1_funct_1(sK4,X3),X4)
      | ~ r1_tarski(k9_relat_1(sK4,sK2),X4) ) ),
    inference(resolution,[],[f97,f57])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK4,X0),k9_relat_1(sK4,sK2))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f96,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(k1_funct_1(X1,X4),X0) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (20184)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (20176)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (20192)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (20169)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (20177)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (20173)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (20171)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (20172)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (20176)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f280,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ~r1_tarski(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ~r1_tarski(sK2,sK3) & v2_funct_1(sK4) & r1_tarski(sK2,k1_relat_1(sK4)) & r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK2,sK3) & v2_funct_1(sK4) & r1_tarski(sK2,k1_relat_1(sK4)) & r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    r1_tarski(sK2,sK3)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f277])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    r1_tarski(sK2,sK3) | r1_tarski(sK2,sK3)),
% 0.21/0.51    inference(resolution,[],[f273,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK6(sK2,X0),sK3) | r1_tarski(sK2,X0)) )),
% 0.21/0.51    inference(resolution,[],[f272,f172])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ( ! [X14,X15,X13] : (~r1_tarski(X13,k10_relat_1(sK4,k9_relat_1(sK4,X15))) | r2_hidden(sK6(X13,X14),X15) | r1_tarski(X13,X14)) )),
% 0.21/0.51    inference(resolution,[],[f74,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f81,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v1_relat_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) | ~v1_relat_1(sK4)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f80,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 0.21/0.51    inference(resolution,[],[f53,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    v2_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X10,X8,X7,X9] : (~r1_tarski(X8,X10) | r1_tarski(X7,X9) | r2_hidden(sK6(X7,X9),X10) | ~r1_tarski(X7,X8)) )),
% 0.21/0.51    inference(resolution,[],[f69,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f57,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK3)))),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f269])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK3))) | r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK3)))),
% 0.21/0.51    inference(resolution,[],[f267,f59])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK6(sK2,X0),k10_relat_1(sK4,k9_relat_1(sK4,sK3))) | r1_tarski(sK2,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f266,f36])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(sK2,X0) | r2_hidden(sK6(sK2,X0),k10_relat_1(sK4,k9_relat_1(sK4,sK3))) | ~v1_relat_1(sK4)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f265,f37])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(sK2,X0) | r2_hidden(sK6(sK2,X0),k10_relat_1(sK4,k9_relat_1(sK4,sK3))) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 0.21/0.51    inference(resolution,[],[f261,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(definition_folding,[],[f12,f20,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0)))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ( ! [X0] : (~sP1(sK4) | r1_tarski(sK2,X0) | r2_hidden(sK6(sK2,X0),k10_relat_1(sK4,k9_relat_1(sK4,sK3)))) )),
% 0.21/0.51    inference(resolution,[],[f256,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP0(X1,X0,k10_relat_1(X0,X1)) | ~sP1(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k10_relat_1(X0,X1) != X2 | ~sP1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k10_relat_1(X0,X1) != X2)) | ~sP1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~sP0(k9_relat_1(sK4,sK3),sK4,X6) | r2_hidden(sK6(sK2,X5),X6) | r1_tarski(sK2,X5)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f255,f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ( ! [X3] : (r2_hidden(sK6(sK2,X3),k1_relat_1(sK4)) | r1_tarski(sK2,X3)) )),
% 0.21/0.51    inference(resolution,[],[f71,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    sP0(k9_relat_1(sK4,sK2),sK4,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f95,f36])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    sP0(k9_relat_1(sK4,sK2),sK4,sK2) | ~v1_relat_1(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f94,f37])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    sP0(k9_relat_1(sK4,sK2),sK4,sK2) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.52    inference(resolution,[],[f92,f50])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ~sP1(sK4) | sP0(k9_relat_1(sK4,sK2),sK4,sK2)),
% 0.21/0.52    inference(superposition,[],[f60,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    sK2 = k10_relat_1(sK4,k9_relat_1(sK4,sK2))),
% 0.21/0.52    inference(resolution,[],[f83,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    r1_tarski(sK2,k1_relat_1(sK4))),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK4)) | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f79,f82])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK4)) | ~r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0) )),
% 0.21/0.52    inference(resolution,[],[f78,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK4,k9_relat_1(sK4,X0))) | ~r1_tarski(X0,k1_relat_1(sK4))) )),
% 0.21/0.52    inference(resolution,[],[f52,f36])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~sP0(X3,X2,X0) | r2_hidden(sK6(X0,X1),k1_relat_1(X2)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f44,f58])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,k1_relat_1(X1)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X1,X4),X0) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X1,X4),X0) & r2_hidden(X4,k1_relat_1(X1))) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X1,X3),X0) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X1,X3),X0) & r2_hidden(X3,k1_relat_1(X1))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1))) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k1_funct_1(X1,X3),X0) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X1,X3),X0) & r2_hidden(X3,k1_relat_1(X1))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X1,X4),X0) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X1,X4),X0) & r2_hidden(X4,k1_relat_1(X1))) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.52    inference(nnf_transformation,[],[f19])).
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    ( ! [X6,X5] : (r1_tarski(sK2,X5) | r2_hidden(sK6(sK2,X5),X6) | ~r2_hidden(sK6(sK2,X5),k1_relat_1(sK4)) | ~sP0(k9_relat_1(sK4,sK3),sK4,X6)) )),
% 0.21/0.52    inference(resolution,[],[f250,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(k1_funct_1(X1,X4),X0) | r2_hidden(X4,X2) | ~r2_hidden(X4,k1_relat_1(X1)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,sK6(sK2,X0)),k9_relat_1(sK4,sK3)) | r1_tarski(sK2,X0)) )),
% 0.21/0.52    inference(resolution,[],[f161,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK4,sK2),X1) | r2_hidden(k1_funct_1(sK4,sK6(sK2,X0)),X1) | r1_tarski(sK2,X0)) )),
% 0.21/0.52    inference(resolution,[],[f107,f58])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X4,X3] : (~r2_hidden(X3,sK2) | r2_hidden(k1_funct_1(sK4,X3),X4) | ~r1_tarski(k9_relat_1(sK4,sK2),X4)) )),
% 0.21/0.52    inference(resolution,[],[f97,f57])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,X0),k9_relat_1(sK4,sK2)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.52    inference(resolution,[],[f96,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(k1_funct_1(X1,X4),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (20176)------------------------------
% 0.21/0.52  % (20176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20176)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (20176)Memory used [KB]: 6524
% 0.21/0.52  % (20176)Time elapsed: 0.096 s
% 0.21/0.52  % (20176)------------------------------
% 0.21/0.52  % (20176)------------------------------
% 0.21/0.52  % (20168)Success in time 0.156 s
%------------------------------------------------------------------------------
