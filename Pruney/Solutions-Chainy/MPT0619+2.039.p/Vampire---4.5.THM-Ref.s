%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 325 expanded)
%              Number of leaves         :   13 (  90 expanded)
%              Depth                    :   21
%              Number of atoms          :  306 (1349 expanded)
%              Number of equality atoms :   78 ( 497 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f484,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f233,f238,f483])).

fof(f483,plain,
    ( spl13_7
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f482,f217,f190])).

fof(f190,plain,
    ( spl13_7
  <=> ! [X0] : ~ sP0(X0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f217,plain,
    ( spl13_12
  <=> sP2(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f482,plain,
    ( ! [X0] : ~ sP0(X0,sK7)
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f481,f297])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ sP1(sK7,k1_tarski(X0))
        | ~ sP0(X0,sK7) )
    | ~ spl13_12 ),
    inference(resolution,[],[f290,f96])).

fof(f96,plain,(
    ! [X0] : sP3(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP3(X0,X1) )
      & ( sP3(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP3(X0,X1) ) ),
    inference(definition_folding,[],[f1,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f290,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X1,X0)
        | ~ sP0(X1,sK7)
        | ~ sP1(sK7,X0) )
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f289,f218])).

fof(f218,plain,
    ( sP2(sK7)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f217])).

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ sP3(X1,X0)
      | ~ sP0(X1,sK7)
      | ~ sP1(sK7,X0)
      | ~ sP2(sK7) ) ),
    inference(superposition,[],[f287,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | ~ sP1(X0,X1)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f287,plain,(
    ! [X0] :
      ( ~ sP3(X0,k2_relat_1(sK7))
      | ~ sP0(X0,sK7) ) ),
    inference(equality_resolution,[],[f256])).

fof(f256,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK7) != X1
      | ~ sP3(X0,X1)
      | ~ sP0(X0,sK7) ) ),
    inference(superposition,[],[f121,f252])).

fof(f252,plain,(
    ! [X2] :
      ( k1_funct_1(sK7,sK6) = X2
      | ~ sP0(X2,sK7) ) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,(
    ! [X2] :
      ( k1_funct_1(sK7,sK6) = X2
      | ~ sP0(X2,sK7)
      | ~ sP0(X2,sK7) ) ),
    inference(superposition,[],[f73,f167])).

fof(f167,plain,(
    ! [X1] :
      ( sK6 = sK9(X1,sK7)
      | ~ sP0(X1,sK7) ) ),
    inference(resolution,[],[f165,f150])).

fof(f150,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0,sK7),k1_tarski(sK6))
      | ~ sP0(X0,sK7) ) ),
    inference(superposition,[],[f72,f60])).

fof(f60,plain,(
    k1_tarski(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k2_relat_1(sK7) != k1_tarski(k1_funct_1(sK7,sK6))
    & k1_tarski(sK6) = k1_relat_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f13,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK7) != k1_tarski(k1_funct_1(sK7,sK6))
      & k1_tarski(sK6) = k1_relat_1(sK7)
      & v1_funct_1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK9(X0,X1)) = X0
          & r2_hidden(sK9(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK9(X0,X1)) = X0
        & r2_hidden(sK9(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f79,f96])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ( sK11(X0,X1) != X0
            | ~ r2_hidden(sK11(X0,X1),X1) )
          & ( sK11(X0,X1) = X0
            | r2_hidden(sK11(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK11(X0,X1) != X0
          | ~ r2_hidden(sK11(X0,X1),X1) )
        & ( sK11(X0,X1) = X0
          | r2_hidden(sK11(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK9(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f121,plain,(
    ! [X0] :
      ( ~ sP3(k1_funct_1(sK7,sK6),X0)
      | k2_relat_1(sK7) != X0 ) ),
    inference(superposition,[],[f61,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f61,plain,(
    k2_relat_1(sK7) != k1_tarski(k1_funct_1(sK7,sK6)) ),
    inference(cnf_transformation,[],[f34])).

fof(f481,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK7)
      | sP1(sK7,k1_tarski(X0)) ) ),
    inference(condensation,[],[f480])).

fof(f480,plain,(
    ! [X8,X9] :
      ( ~ sP0(X8,sK7)
      | sP1(sK7,k1_tarski(X8))
      | ~ sP0(X9,sK7) ) ),
    inference(subsumption_resolution,[],[f479,f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,sK7)
      | X0 = X1
      | ~ sP0(X0,sK7) ) ),
    inference(superposition,[],[f252,f252])).

fof(f479,plain,(
    ! [X8,X9] :
      ( ~ sP0(X8,sK7)
      | sP1(sK7,k1_tarski(X8))
      | ~ sP0(X9,sK7)
      | X8 != X9 ) ),
    inference(subsumption_resolution,[],[f474,f119])).

fof(f119,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f95,f96])).

fof(f95,plain,(
    ! [X3,X1] :
      ( ~ sP3(X3,X1)
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f474,plain,(
    ! [X8,X9] :
      ( ~ sP0(X8,sK7)
      | sP1(sK7,k1_tarski(X8))
      | ~ r2_hidden(X8,k1_tarski(X8))
      | ~ sP0(X9,sK7)
      | X8 != X9 ) ),
    inference(duplicate_literal_removal,[],[f471])).

fof(f471,plain,(
    ! [X8,X9] :
      ( ~ sP0(X8,sK7)
      | sP1(sK7,k1_tarski(X8))
      | ~ r2_hidden(X8,k1_tarski(X8))
      | sP1(sK7,k1_tarski(X8))
      | ~ sP0(X9,sK7)
      | X8 != X9 ) ),
    inference(superposition,[],[f71,f458])).

fof(f458,plain,(
    ! [X0,X1] :
      ( sK8(sK7,k1_tarski(X0)) = X0
      | sP1(sK7,k1_tarski(X0))
      | ~ sP0(X1,sK7)
      | X0 != X1 ) ),
    inference(equality_factoring,[],[f413])).

fof(f413,plain,(
    ! [X2,X3] :
      ( sK8(sK7,k1_tarski(X2)) = X3
      | sP1(sK7,k1_tarski(X2))
      | ~ sP0(X3,sK7)
      | sK8(sK7,k1_tarski(X2)) = X2 ) ),
    inference(resolution,[],[f393,f165])).

fof(f393,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK8(sK7,X1),X1)
      | sP1(sK7,X1)
      | sK8(sK7,X1) = X2
      | ~ sP0(X2,sK7) ) ),
    inference(resolution,[],[f70,f254])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sP0(sK8(X0,X1),X0)
      | sP1(X0,X1)
      | r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK8(X0,X1),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( sP0(sK8(X0,X1),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK8(X0,X1),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( sP0(sK8(X0,X1),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK8(X0,X1),X0)
      | sP1(X0,X1)
      | ~ r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f238,plain,(
    ~ spl13_7 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl13_7 ),
    inference(resolution,[],[f228,f119])).

fof(f228,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_tarski(sK6))
    | ~ spl13_7 ),
    inference(forward_demodulation,[],[f225,f60])).

fof(f225,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_relat_1(sK7))
    | ~ spl13_7 ),
    inference(resolution,[],[f94,f191])).

fof(f191,plain,
    ( ! [X0] : ~ sP0(X0,sK7)
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f190])).

fof(f94,plain,(
    ! [X2,X1] :
      ( sP0(k1_funct_1(X1,X2),X1)
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | k1_funct_1(X1,X2) != X0
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f233,plain,(
    spl13_12 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl13_12 ),
    inference(subsumption_resolution,[],[f231,f58])).

fof(f58,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f231,plain,
    ( ~ v1_relat_1(sK7)
    | spl13_12 ),
    inference(subsumption_resolution,[],[f230,f59])).

fof(f59,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f230,plain,
    ( ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl13_12 ),
    inference(resolution,[],[f219,f75])).

fof(f75,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f17,f26,f25,f24])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f219,plain,
    ( ~ sP2(sK7)
    | spl13_12 ),
    inference(avatar_component_clause,[],[f217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:16:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (25844)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (25845)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (25865)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (25846)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (25861)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (25857)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (25867)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (25849)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (25851)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (25847)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (25863)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (25868)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (25855)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (25847)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (25864)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (25848)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.26/0.52  % (25843)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.26/0.52  % (25854)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.26/0.52  % (25850)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.26/0.53  % (25850)Refutation not found, incomplete strategy% (25850)------------------------------
% 1.26/0.53  % (25850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (25850)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (25850)Memory used [KB]: 1663
% 1.26/0.53  % (25850)Time elapsed: 0.106 s
% 1.26/0.53  % (25850)------------------------------
% 1.26/0.53  % (25850)------------------------------
% 1.26/0.53  % (25852)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.26/0.53  % (25853)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.26/0.53  % (25860)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.26/0.53  % (25866)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.26/0.53  % (25862)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.26/0.54  % (25856)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.26/0.54  % (25858)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.26/0.54  % SZS output start Proof for theBenchmark
% 1.26/0.54  fof(f484,plain,(
% 1.26/0.54    $false),
% 1.26/0.54    inference(avatar_sat_refutation,[],[f233,f238,f483])).
% 1.26/0.54  fof(f483,plain,(
% 1.26/0.54    spl13_7 | ~spl13_12),
% 1.26/0.54    inference(avatar_split_clause,[],[f482,f217,f190])).
% 1.26/0.54  fof(f190,plain,(
% 1.26/0.54    spl13_7 <=> ! [X0] : ~sP0(X0,sK7)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 1.26/0.54  fof(f217,plain,(
% 1.26/0.54    spl13_12 <=> sP2(sK7)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).
% 1.26/0.54  fof(f482,plain,(
% 1.26/0.54    ( ! [X0] : (~sP0(X0,sK7)) ) | ~spl13_12),
% 1.26/0.54    inference(subsumption_resolution,[],[f481,f297])).
% 1.26/0.54  fof(f297,plain,(
% 1.26/0.54    ( ! [X0] : (~sP1(sK7,k1_tarski(X0)) | ~sP0(X0,sK7)) ) | ~spl13_12),
% 1.26/0.54    inference(resolution,[],[f290,f96])).
% 1.26/0.54  fof(f96,plain,(
% 1.26/0.54    ( ! [X0] : (sP3(X0,k1_tarski(X0))) )),
% 1.26/0.54    inference(equality_resolution,[],[f83])).
% 1.26/0.54  fof(f83,plain,(
% 1.26/0.54    ( ! [X0,X1] : (sP3(X0,X1) | k1_tarski(X0) != X1) )),
% 1.26/0.54    inference(cnf_transformation,[],[f50])).
% 1.26/0.54  fof(f50,plain,(
% 1.26/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP3(X0,X1)) & (sP3(X0,X1) | k1_tarski(X0) != X1))),
% 1.26/0.54    inference(nnf_transformation,[],[f29])).
% 1.26/0.54  fof(f29,plain,(
% 1.26/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP3(X0,X1))),
% 1.26/0.54    inference(definition_folding,[],[f1,f28])).
% 1.26/0.54  fof(f28,plain,(
% 1.26/0.54    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.26/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.26/0.54  fof(f1,axiom,(
% 1.26/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.26/0.54  fof(f290,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~sP3(X1,X0) | ~sP0(X1,sK7) | ~sP1(sK7,X0)) ) | ~spl13_12),
% 1.26/0.54    inference(subsumption_resolution,[],[f289,f218])).
% 1.26/0.54  fof(f218,plain,(
% 1.26/0.54    sP2(sK7) | ~spl13_12),
% 1.26/0.54    inference(avatar_component_clause,[],[f217])).
% 1.26/0.54  fof(f289,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~sP3(X1,X0) | ~sP0(X1,sK7) | ~sP1(sK7,X0) | ~sP2(sK7)) )),
% 1.26/0.54    inference(superposition,[],[f287,f67])).
% 1.26/0.54  fof(f67,plain,(
% 1.26/0.54    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | ~sP1(X0,X1) | ~sP2(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f35])).
% 1.26/0.54  fof(f35,plain,(
% 1.26/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 1.26/0.54    inference(nnf_transformation,[],[f26])).
% 1.26/0.54  fof(f26,plain,(
% 1.26/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 1.26/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.26/0.54  fof(f287,plain,(
% 1.26/0.54    ( ! [X0] : (~sP3(X0,k2_relat_1(sK7)) | ~sP0(X0,sK7)) )),
% 1.26/0.54    inference(equality_resolution,[],[f256])).
% 1.26/0.54  fof(f256,plain,(
% 1.26/0.54    ( ! [X0,X1] : (k2_relat_1(sK7) != X1 | ~sP3(X0,X1) | ~sP0(X0,sK7)) )),
% 1.26/0.54    inference(superposition,[],[f121,f252])).
% 1.26/0.54  fof(f252,plain,(
% 1.26/0.54    ( ! [X2] : (k1_funct_1(sK7,sK6) = X2 | ~sP0(X2,sK7)) )),
% 1.26/0.54    inference(duplicate_literal_removal,[],[f248])).
% 1.26/0.54  fof(f248,plain,(
% 1.26/0.54    ( ! [X2] : (k1_funct_1(sK7,sK6) = X2 | ~sP0(X2,sK7) | ~sP0(X2,sK7)) )),
% 1.26/0.54    inference(superposition,[],[f73,f167])).
% 1.26/0.54  fof(f167,plain,(
% 1.26/0.54    ( ! [X1] : (sK6 = sK9(X1,sK7) | ~sP0(X1,sK7)) )),
% 1.26/0.54    inference(resolution,[],[f165,f150])).
% 1.26/0.54  fof(f150,plain,(
% 1.26/0.54    ( ! [X0] : (r2_hidden(sK9(X0,sK7),k1_tarski(sK6)) | ~sP0(X0,sK7)) )),
% 1.26/0.54    inference(superposition,[],[f72,f60])).
% 1.26/0.54  fof(f60,plain,(
% 1.26/0.54    k1_tarski(sK6) = k1_relat_1(sK7)),
% 1.26/0.54    inference(cnf_transformation,[],[f34])).
% 1.26/0.54  fof(f34,plain,(
% 1.26/0.54    k2_relat_1(sK7) != k1_tarski(k1_funct_1(sK7,sK6)) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7)),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f13,f33])).
% 1.26/0.54  fof(f33,plain,(
% 1.26/0.54    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK7) != k1_tarski(k1_funct_1(sK7,sK6)) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f13,plain,(
% 1.26/0.54    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.26/0.54    inference(flattening,[],[f12])).
% 1.26/0.54  fof(f12,plain,(
% 1.26/0.54    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.26/0.54    inference(ennf_transformation,[],[f11])).
% 1.26/0.54  fof(f11,negated_conjecture,(
% 1.26/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.26/0.54    inference(negated_conjecture,[],[f10])).
% 1.26/0.54  fof(f10,conjecture,(
% 1.26/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.26/0.54  fof(f72,plain,(
% 1.26/0.54    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),k1_relat_1(X1)) | ~sP0(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f43])).
% 1.26/0.54  fof(f43,plain,(
% 1.26/0.54    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK9(X0,X1)) = X0 & r2_hidden(sK9(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).
% 1.26/0.54  fof(f42,plain,(
% 1.26/0.54    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK9(X0,X1)) = X0 & r2_hidden(sK9(X0,X1),k1_relat_1(X1))))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f41,plain,(
% 1.26/0.54    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 1.26/0.54    inference(rectify,[],[f40])).
% 1.26/0.54  fof(f40,plain,(
% 1.26/0.54    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 1.26/0.54    inference(nnf_transformation,[],[f24])).
% 1.26/0.54  fof(f24,plain,(
% 1.26/0.54    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 1.26/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.26/0.54  fof(f165,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 1.26/0.54    inference(resolution,[],[f79,f96])).
% 1.26/0.54  fof(f79,plain,(
% 1.26/0.54    ( ! [X0,X3,X1] : (~sP3(X0,X1) | ~r2_hidden(X3,X1) | X0 = X3) )),
% 1.26/0.54    inference(cnf_transformation,[],[f49])).
% 1.26/0.54  fof(f49,plain,(
% 1.26/0.54    ! [X0,X1] : ((sP3(X0,X1) | ((sK11(X0,X1) != X0 | ~r2_hidden(sK11(X0,X1),X1)) & (sK11(X0,X1) = X0 | r2_hidden(sK11(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f47,f48])).
% 1.26/0.54  fof(f48,plain,(
% 1.26/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK11(X0,X1) != X0 | ~r2_hidden(sK11(X0,X1),X1)) & (sK11(X0,X1) = X0 | r2_hidden(sK11(X0,X1),X1))))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f47,plain,(
% 1.26/0.54    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 1.26/0.54    inference(rectify,[],[f46])).
% 1.26/0.54  fof(f46,plain,(
% 1.26/0.54    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP3(X0,X1)))),
% 1.26/0.54    inference(nnf_transformation,[],[f28])).
% 1.26/0.54  fof(f73,plain,(
% 1.26/0.54    ( ! [X0,X1] : (k1_funct_1(X1,sK9(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f43])).
% 1.26/0.54  fof(f121,plain,(
% 1.26/0.54    ( ! [X0] : (~sP3(k1_funct_1(sK7,sK6),X0) | k2_relat_1(sK7) != X0) )),
% 1.26/0.54    inference(superposition,[],[f61,f84])).
% 1.26/0.54  fof(f84,plain,(
% 1.26/0.54    ( ! [X0,X1] : (k1_tarski(X0) = X1 | ~sP3(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f50])).
% 1.26/0.54  fof(f61,plain,(
% 1.26/0.54    k2_relat_1(sK7) != k1_tarski(k1_funct_1(sK7,sK6))),
% 1.26/0.54    inference(cnf_transformation,[],[f34])).
% 1.26/0.54  fof(f481,plain,(
% 1.26/0.54    ( ! [X0] : (~sP0(X0,sK7) | sP1(sK7,k1_tarski(X0))) )),
% 1.26/0.54    inference(condensation,[],[f480])).
% 1.26/0.54  fof(f480,plain,(
% 1.26/0.54    ( ! [X8,X9] : (~sP0(X8,sK7) | sP1(sK7,k1_tarski(X8)) | ~sP0(X9,sK7)) )),
% 1.26/0.54    inference(subsumption_resolution,[],[f479,f254])).
% 1.26/0.54  fof(f254,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~sP0(X1,sK7) | X0 = X1 | ~sP0(X0,sK7)) )),
% 1.26/0.54    inference(superposition,[],[f252,f252])).
% 1.26/0.54  fof(f479,plain,(
% 1.26/0.54    ( ! [X8,X9] : (~sP0(X8,sK7) | sP1(sK7,k1_tarski(X8)) | ~sP0(X9,sK7) | X8 != X9) )),
% 1.26/0.54    inference(subsumption_resolution,[],[f474,f119])).
% 1.26/0.54  fof(f119,plain,(
% 1.26/0.54    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.26/0.54    inference(resolution,[],[f95,f96])).
% 1.26/0.54  fof(f95,plain,(
% 1.26/0.54    ( ! [X3,X1] : (~sP3(X3,X1) | r2_hidden(X3,X1)) )),
% 1.26/0.54    inference(equality_resolution,[],[f80])).
% 1.26/0.54  fof(f80,plain,(
% 1.26/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | ~sP3(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f49])).
% 1.26/0.54  fof(f474,plain,(
% 1.26/0.54    ( ! [X8,X9] : (~sP0(X8,sK7) | sP1(sK7,k1_tarski(X8)) | ~r2_hidden(X8,k1_tarski(X8)) | ~sP0(X9,sK7) | X8 != X9) )),
% 1.26/0.54    inference(duplicate_literal_removal,[],[f471])).
% 1.26/0.54  fof(f471,plain,(
% 1.26/0.54    ( ! [X8,X9] : (~sP0(X8,sK7) | sP1(sK7,k1_tarski(X8)) | ~r2_hidden(X8,k1_tarski(X8)) | sP1(sK7,k1_tarski(X8)) | ~sP0(X9,sK7) | X8 != X9) )),
% 1.26/0.54    inference(superposition,[],[f71,f458])).
% 1.26/0.54  fof(f458,plain,(
% 1.26/0.54    ( ! [X0,X1] : (sK8(sK7,k1_tarski(X0)) = X0 | sP1(sK7,k1_tarski(X0)) | ~sP0(X1,sK7) | X0 != X1) )),
% 1.26/0.54    inference(equality_factoring,[],[f413])).
% 1.26/0.54  fof(f413,plain,(
% 1.26/0.54    ( ! [X2,X3] : (sK8(sK7,k1_tarski(X2)) = X3 | sP1(sK7,k1_tarski(X2)) | ~sP0(X3,sK7) | sK8(sK7,k1_tarski(X2)) = X2) )),
% 1.26/0.54    inference(resolution,[],[f393,f165])).
% 1.26/0.54  fof(f393,plain,(
% 1.26/0.54    ( ! [X2,X1] : (r2_hidden(sK8(sK7,X1),X1) | sP1(sK7,X1) | sK8(sK7,X1) = X2 | ~sP0(X2,sK7)) )),
% 1.26/0.54    inference(resolution,[],[f70,f254])).
% 1.26/0.54  fof(f70,plain,(
% 1.26/0.54    ( ! [X0,X1] : (sP0(sK8(X0,X1),X0) | sP1(X0,X1) | r2_hidden(sK8(X0,X1),X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f39])).
% 1.26/0.54  fof(f39,plain,(
% 1.26/0.54    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK8(X0,X1),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (sP0(sK8(X0,X1),X0) | r2_hidden(sK8(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f38])).
% 1.26/0.54  fof(f38,plain,(
% 1.26/0.54    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK8(X0,X1),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (sP0(sK8(X0,X1),X0) | r2_hidden(sK8(X0,X1),X1))))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f37,plain,(
% 1.26/0.54    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.26/0.54    inference(rectify,[],[f36])).
% 1.26/0.54  fof(f36,plain,(
% 1.26/0.54    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 1.26/0.54    inference(nnf_transformation,[],[f25])).
% 1.26/0.54  fof(f25,plain,(
% 1.26/0.54    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 1.26/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.26/0.54  fof(f71,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~sP0(sK8(X0,X1),X0) | sP1(X0,X1) | ~r2_hidden(sK8(X0,X1),X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f39])).
% 1.26/0.54  fof(f238,plain,(
% 1.26/0.54    ~spl13_7),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f235])).
% 1.26/0.54  fof(f235,plain,(
% 1.26/0.54    $false | ~spl13_7),
% 1.26/0.54    inference(resolution,[],[f228,f119])).
% 1.26/0.54  fof(f228,plain,(
% 1.26/0.54    ( ! [X1] : (~r2_hidden(X1,k1_tarski(sK6))) ) | ~spl13_7),
% 1.26/0.54    inference(forward_demodulation,[],[f225,f60])).
% 1.26/0.54  fof(f225,plain,(
% 1.26/0.54    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK7))) ) | ~spl13_7),
% 1.26/0.54    inference(resolution,[],[f94,f191])).
% 1.26/0.54  fof(f191,plain,(
% 1.26/0.54    ( ! [X0] : (~sP0(X0,sK7)) ) | ~spl13_7),
% 1.26/0.54    inference(avatar_component_clause,[],[f190])).
% 1.26/0.54  fof(f94,plain,(
% 1.26/0.54    ( ! [X2,X1] : (sP0(k1_funct_1(X1,X2),X1) | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 1.26/0.54    inference(equality_resolution,[],[f74])).
% 1.26/0.54  fof(f74,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (sP0(X0,X1) | k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f43])).
% 1.26/0.54  fof(f233,plain,(
% 1.26/0.54    spl13_12),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f232])).
% 1.26/0.54  fof(f232,plain,(
% 1.26/0.54    $false | spl13_12),
% 1.26/0.54    inference(subsumption_resolution,[],[f231,f58])).
% 1.26/0.54  fof(f58,plain,(
% 1.26/0.54    v1_relat_1(sK7)),
% 1.26/0.54    inference(cnf_transformation,[],[f34])).
% 1.26/0.54  fof(f231,plain,(
% 1.26/0.54    ~v1_relat_1(sK7) | spl13_12),
% 1.26/0.54    inference(subsumption_resolution,[],[f230,f59])).
% 1.26/0.54  fof(f59,plain,(
% 1.26/0.54    v1_funct_1(sK7)),
% 1.26/0.54    inference(cnf_transformation,[],[f34])).
% 1.26/0.54  fof(f230,plain,(
% 1.26/0.54    ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | spl13_12),
% 1.26/0.54    inference(resolution,[],[f219,f75])).
% 1.26/0.54  fof(f75,plain,(
% 1.26/0.54    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f27])).
% 1.26/0.54  fof(f27,plain,(
% 1.26/0.54    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.54    inference(definition_folding,[],[f17,f26,f25,f24])).
% 1.26/0.54  fof(f17,plain,(
% 1.26/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.54    inference(flattening,[],[f16])).
% 1.26/0.54  fof(f16,plain,(
% 1.26/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f8])).
% 1.26/0.54  fof(f8,axiom,(
% 1.26/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.26/0.54  fof(f219,plain,(
% 1.26/0.54    ~sP2(sK7) | spl13_12),
% 1.26/0.54    inference(avatar_component_clause,[],[f217])).
% 1.26/0.54  % SZS output end Proof for theBenchmark
% 1.26/0.54  % (25847)------------------------------
% 1.26/0.54  % (25847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (25847)Termination reason: Refutation
% 1.26/0.54  
% 1.26/0.54  % (25847)Memory used [KB]: 6268
% 1.26/0.54  % (25847)Time elapsed: 0.106 s
% 1.26/0.54  % (25847)------------------------------
% 1.26/0.54  % (25847)------------------------------
% 1.26/0.55  % (25842)Success in time 0.182 s
%------------------------------------------------------------------------------
