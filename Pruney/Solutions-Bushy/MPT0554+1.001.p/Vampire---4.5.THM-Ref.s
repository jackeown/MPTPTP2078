%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0554+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 101 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  200 ( 411 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f45,f30,f168])).

fof(f168,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(X0,sK3),k9_relat_1(X0,sK4))
      | ~ sP2(X0) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(X0,sK3),k9_relat_1(X0,sK4))
      | ~ sP2(X0)
      | ~ sP2(X0)
      | r1_tarski(k9_relat_1(X0,sK3),k9_relat_1(X0,sK4)) ) ),
    inference(resolution,[],[f99,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,sK8(X2,k9_relat_1(X1,X0)))
      | ~ sP2(X1)
      | r1_tarski(X2,k9_relat_1(X1,X0)) ) ),
    inference(resolution,[],[f63,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k9_relat_1(X1,X0))
      | ~ sP0(X0,X1,X2)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,k9_relat_1(X0,X1))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ~ sP1(X0,X1,X2) )
          & ( sP1(X0,X1,X2)
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> sP1(X0,X1,X2) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X0,X4)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,X0,sK6(X0,X1,X2))
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(X1,X0,sK6(X0,X1,X2))
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,X0,sK6(X0,X1,X2))
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(X1,X0,sK6(X0,X1,X2))
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X0,X3) )
            & ( sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f99,plain,(
    ! [X0,X1] :
      ( sP0(sK4,X0,sK8(k9_relat_1(X0,sK3),X1))
      | r1_tarski(k9_relat_1(X0,sK3),X1)
      | ~ sP2(X0) ) ),
    inference(resolution,[],[f77,f94])).

fof(f94,plain,(
    ! [X8,X9] :
      ( ~ sP0(sK3,X8,X9)
      | sP0(sK4,X8,X9) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X8,X9] :
      ( sP0(sK4,X8,X9)
      | ~ sP0(sK3,X8,X9)
      | ~ sP0(sK3,X8,X9) ) ),
    inference(resolution,[],[f70,f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK7(sK3,X1,X2),sK4)
      | ~ sP0(sK3,X1,X2) ) ),
    inference(resolution,[],[f48,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1) ) )
      & ( ( r2_hidden(sK7(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(sK7(X0,X1,X2),X2),X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X2),X1) )
     => ( r2_hidden(sK7(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,X2),X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X1,X0,X3] :
      ( ( sP0(X1,X0,X3)
        | ! [X4] :
            ( ~ r2_hidden(X4,X1)
            | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X1)
            & r2_hidden(k4_tarski(X4,X3),X0) )
        | ~ sP0(X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X1,X0,X3] :
      ( sP0(X1,X0,X3)
    <=> ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f41,f29])).

fof(f29,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k9_relat_1(sK5,sK3),k9_relat_1(sK5,sK4))
    & r1_tarski(sK3,sK4)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f6,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK5,sK3),k9_relat_1(sK5,sK4))
      & r1_tarski(sK3,sK4)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X3)
      | sP0(X3,X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f39,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X2),X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X1)
      | ~ r2_hidden(X3,X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,sK8(k9_relat_1(X1,X0),X2))
      | ~ sP2(X1)
      | r1_tarski(k9_relat_1(X1,X0),X2) ) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | sP0(X2,X1,X0)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f33,f44])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    ~ r1_tarski(k9_relat_1(sK5,sK3),k9_relat_1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    sP2(sK5) ),
    inference(resolution,[],[f40,f28])).

fof(f28,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | sP2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f7,f11,f10,f9])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

%------------------------------------------------------------------------------
