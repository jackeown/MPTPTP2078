%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1032+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 350 expanded)
%              Number of leaves         :   14 ( 103 expanded)
%              Depth                    :   20
%              Number of atoms          :  333 (1602 expanded)
%              Number of equality atoms :   48 ( 249 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f38])).

fof(f38,plain,(
    ~ r1_tarski(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ~ r1_tarski(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f6,f14])).

fof(f14,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1))
   => ~ r1_tarski(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_2)).

fof(f199,plain,(
    r1_tarski(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)) ),
    inference(resolution,[],[f198,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
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

fof(f198,plain,(
    r2_hidden(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)),k4_partfun1(sK4,sK5)) ),
    inference(resolution,[],[f188,f70])).

fof(f70,plain,(
    ! [X0,X1] : sP3(X0,X1,k4_partfun1(X0,X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k4_partfun1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_partfun1(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k4_partfun1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_partfun1(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f12,f11])).

fof(f11,plain,(
    ! [X1,X0,X3] :
      ( sP2(X1,X0,X3)
    <=> ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X1)
          & r1_tarski(k1_relat_1(X4),X0)
          & X3 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_partfun1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & r1_tarski(k1_relat_1(X4),X0)
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_partfun1)).

fof(f188,plain,(
    ! [X0] :
      ( ~ sP3(sK4,sK5,X0)
      | r2_hidden(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)),X0) ) ),
    inference(resolution,[],[f184,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X1,X0,X4)
      | r2_hidden(X4,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(X1,X0,sK9(X0,X1,X2))
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sP2(X1,X0,sK9(X0,X1,X2))
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X0,X4) )
            & ( sP2(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(X1,X0,sK9(X0,X1,X2))
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sP2(X1,X0,sK9(X0,X1,X2))
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X0,X4) )
            & ( sP2(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X1,X0,X3) )
            & ( sP2(X1,X0,X3)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f184,plain,(
    sP2(sK5,sK4,sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))) ),
    inference(resolution,[],[f173,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f173,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,X0)
      | sP2(sK5,X0,sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))) ) ),
    inference(subsumption_resolution,[],[f162,f169])).

fof(f169,plain,(
    v1_relat_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f168,f38])).

fof(f168,plain,
    ( v1_relat_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)))
    | r1_tarski(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)) ),
    inference(resolution,[],[f148,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,sK6(k1_funct_2(X1,X0),X2))
      | r1_tarski(k1_funct_2(X1,X0),X2) ) ),
    inference(resolution,[],[f76,f68])).

fof(f68,plain,(
    ! [X0,X1] : sP1(X0,X1,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f9,f8])).

fof(f8,plain,(
    ! [X1,X0,X3] :
      ( sP0(X1,X0,X3)
    <=> ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X1)
          & k1_relat_1(X4) = X0
          & X3 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X1,X0,X2)
      | sP0(X0,X1,sK6(X2,X3))
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f42,f40])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | sP0(X1,X0,X4)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,X0,sK7(X0,X1,X2))
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP0(X1,X0,sK7(X0,X1,X2))
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,X0,sK7(X0,X1,X2))
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP0(X1,X0,sK7(X0,X1,X2))
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f148,plain,
    ( ~ sP0(sK5,sK4,sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)))
    | v1_relat_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))) ),
    inference(superposition,[],[f46,f139])).

fof(f139,plain,(
    sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)) = sK8(sK5,sK4,sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))) ),
    inference(resolution,[],[f88,f38])).

fof(f88,plain,(
    ! [X12,X10,X11] :
      ( r1_tarski(k1_funct_2(X10,X11),X12)
      | sK6(k1_funct_2(X10,X11),X12) = sK8(X11,X10,sK6(k1_funct_2(X10,X11),X12)) ) ),
    inference(resolution,[],[f83,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK8(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X0)
          & k1_relat_1(sK8(X0,X1,X2)) = X1
          & sK8(X0,X1,X2) = X2
          & v1_funct_1(sK8(X0,X1,X2))
          & v1_relat_1(sK8(X0,X1,X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X0)
          & k1_relat_1(X4) = X1
          & X2 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
     => ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X0)
        & k1_relat_1(sK8(X0,X1,X2)) = X1
        & sK8(X0,X1,X2) = X2
        & v1_funct_1(sK8(X0,X1,X2))
        & v1_relat_1(sK8(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X0)
            & k1_relat_1(X4) = X1
            & X2 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X3] :
      ( ( sP0(X1,X0,X3)
        | ! [X4] :
            ( ~ r1_tarski(k2_relat_1(X4),X1)
            | k1_relat_1(X4) != X0
            | X3 != X4
            | ~ v1_funct_1(X4)
            | ~ v1_relat_1(X4) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X1)
            & k1_relat_1(X4) = X0
            & X3 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP0(X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f162,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,X0)
      | sP2(sK5,X0,sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)))
      | ~ v1_relat_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))) ) ),
    inference(subsumption_resolution,[],[f153,f160])).

fof(f160,plain,(
    v1_funct_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f159,f38])).

fof(f159,plain,
    ( v1_funct_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)))
    | r1_tarski(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)) ),
    inference(resolution,[],[f147,f83])).

fof(f147,plain,
    ( ~ sP0(sK5,sK4,sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)))
    | v1_funct_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))) ),
    inference(superposition,[],[f47,f139])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f153,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,X0)
      | sP2(sK5,X0,sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)))
      | ~ v1_funct_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)))
      | ~ v1_relat_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))) ) ),
    inference(forward_demodulation,[],[f150,f142])).

fof(f142,plain,(
    sK4 = k1_relat_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))) ),
    inference(backward_demodulation,[],[f102,f139])).

fof(f102,plain,(
    sK4 = k1_relat_1(sK8(sK5,sK4,sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)))) ),
    inference(resolution,[],[f86,f38])).

fof(f86,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k1_funct_2(X3,X4),X5)
      | k1_relat_1(sK8(X4,X3,sK6(k1_funct_2(X3,X4),X5))) = X3 ) ),
    inference(resolution,[],[f83,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_relat_1(sK8(X0,X1,X2)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f150,plain,(
    ! [X0] :
      ( sP2(sK5,X0,sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)))
      | ~ r1_tarski(k1_relat_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))),X0)
      | ~ v1_funct_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)))
      | ~ v1_relat_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))) ) ),
    inference(resolution,[],[f149,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X0)
      | sP2(X0,X1,X3)
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2)
      | ~ r1_tarski(k2_relat_1(X3),X0)
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | X2 != X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | ~ r1_tarski(k1_relat_1(X3),X1)
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ( r1_tarski(k2_relat_1(sK10(X0,X1,X2)),X0)
          & r1_tarski(k1_relat_1(sK10(X0,X1,X2)),X1)
          & sK10(X0,X1,X2) = X2
          & v1_funct_1(sK10(X0,X1,X2))
          & v1_relat_1(sK10(X0,X1,X2)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X0)
          & r1_tarski(k1_relat_1(X4),X1)
          & X2 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
     => ( r1_tarski(k2_relat_1(sK10(X0,X1,X2)),X0)
        & r1_tarski(k1_relat_1(sK10(X0,X1,X2)),X1)
        & sK10(X0,X1,X2) = X2
        & v1_funct_1(sK10(X0,X1,X2))
        & v1_relat_1(sK10(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | ~ r1_tarski(k1_relat_1(X3),X1)
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X0)
            & r1_tarski(k1_relat_1(X4),X1)
            & X2 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X3] :
      ( ( sP2(X1,X0,X3)
        | ! [X4] :
            ( ~ r1_tarski(k2_relat_1(X4),X1)
            | ~ r1_tarski(k1_relat_1(X4),X0)
            | X3 != X4
            | ~ v1_funct_1(X4)
            | ~ v1_relat_1(X4) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X1)
            & r1_tarski(k1_relat_1(X4),X0)
            & X3 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP2(X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f149,plain,(
    r1_tarski(k2_relat_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))),sK5) ),
    inference(subsumption_resolution,[],[f146,f38])).

fof(f146,plain,
    ( r1_tarski(k2_relat_1(sK6(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5))),sK5)
    | r1_tarski(k1_funct_2(sK4,sK5),k4_partfun1(sK4,sK5)) ),
    inference(superposition,[],[f85,f139])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X1,X0,sK6(k1_funct_2(X0,X1),X2))),X1)
      | r1_tarski(k1_funct_2(X0,X1),X2) ) ),
    inference(resolution,[],[f83,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X0) ) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
