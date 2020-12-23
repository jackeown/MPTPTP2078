%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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
fof(f341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f161,f197,f340])).

fof(f340,plain,
    ( spl11_1
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f339,f187,f96])).

fof(f96,plain,
    ( spl11_1
  <=> ! [X3] : ~ sP0(X3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f187,plain,
    ( spl11_8
  <=> sP2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f339,plain,
    ( ! [X0] : ~ sP0(X0,sK5)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f338,f209])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ sP1(sK5,k1_tarski(X0))
        | ~ sP0(X0,sK5) )
    | ~ spl11_8 ),
    inference(resolution,[],[f208,f71])).

fof(f71,plain,(
    ! [X0] : sP3(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP3(X0,X1) )
      & ( sP3(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP3(X0,X1) ) ),
    inference(definition_folding,[],[f1,f21])).

fof(f21,plain,(
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

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X1,X0)
        | ~ sP0(X1,sK5)
        | ~ sP1(sK5,X0) )
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f207,f188])).

fof(f188,plain,
    ( sP2(sK5)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f187])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ sP3(X1,X0)
      | ~ sP0(X1,sK5)
      | ~ sP1(sK5,X0)
      | ~ sP2(sK5) ) ),
    inference(superposition,[],[f205,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | ~ sP1(X0,X1)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f205,plain,(
    ! [X0] :
      ( ~ sP3(X0,k2_relat_1(sK5))
      | ~ sP0(X0,sK5) ) ),
    inference(equality_resolution,[],[f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK5) != X1
      | ~ sP3(X0,X1)
      | ~ sP0(X0,sK5) ) ),
    inference(superposition,[],[f75,f178])).

fof(f178,plain,(
    ! [X2] :
      ( k1_funct_1(sK5,sK4) = X2
      | ~ sP0(X2,sK5) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X2] :
      ( k1_funct_1(sK5,sK4) = X2
      | ~ sP0(X2,sK5)
      | ~ sP0(X2,sK5) ) ),
    inference(superposition,[],[f54,f114])).

fof(f114,plain,(
    ! [X1] :
      ( sK4 = sK7(X1,sK5)
      | ~ sP0(X1,sK5) ) ),
    inference(resolution,[],[f109,f86])).

fof(f86,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0,sK5),k1_tarski(sK4))
      | ~ sP0(X0,sK5) ) ),
    inference(superposition,[],[f53,f45])).

fof(f45,plain,(
    k1_tarski(sK4) = k1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_relat_1(sK5) != k1_tarski(k1_funct_1(sK5,sK4))
    & k1_tarski(sK4) = k1_relat_1(sK5)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK5) != k1_tarski(k1_funct_1(sK5,sK4))
      & k1_tarski(sK4) = k1_relat_1(sK5)
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK7(X0,X1)) = X0
          & r2_hidden(sK7(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK7(X0,X1)) = X0
        & r2_hidden(sK7(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f60,f71])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK7(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X0] :
      ( ~ sP3(k1_funct_1(sK5,sK4),X0)
      | k2_relat_1(sK5) != X0 ) ),
    inference(superposition,[],[f46,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f46,plain,(
    k2_relat_1(sK5) != k1_tarski(k1_funct_1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f338,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK5)
      | sP1(sK5,k1_tarski(X0)) ) ),
    inference(condensation,[],[f337])).

fof(f337,plain,(
    ! [X8,X9] :
      ( ~ sP0(X8,sK5)
      | sP1(sK5,k1_tarski(X8))
      | ~ sP0(X9,sK5) ) ),
    inference(subsumption_resolution,[],[f336,f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,sK5)
      | X0 = X1
      | ~ sP0(X0,sK5) ) ),
    inference(superposition,[],[f178,f178])).

fof(f336,plain,(
    ! [X8,X9] :
      ( ~ sP0(X8,sK5)
      | sP1(sK5,k1_tarski(X8))
      | ~ sP0(X9,sK5)
      | X8 != X9 ) ),
    inference(subsumption_resolution,[],[f331,f73])).

fof(f73,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f70,f71])).

fof(f70,plain,(
    ! [X3,X1] :
      ( ~ sP3(X3,X1)
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f331,plain,(
    ! [X8,X9] :
      ( ~ sP0(X8,sK5)
      | sP1(sK5,k1_tarski(X8))
      | ~ r2_hidden(X8,k1_tarski(X8))
      | ~ sP0(X9,sK5)
      | X8 != X9 ) ),
    inference(duplicate_literal_removal,[],[f328])).

fof(f328,plain,(
    ! [X8,X9] :
      ( ~ sP0(X8,sK5)
      | sP1(sK5,k1_tarski(X8))
      | ~ r2_hidden(X8,k1_tarski(X8))
      | sP1(sK5,k1_tarski(X8))
      | ~ sP0(X9,sK5)
      | X8 != X9 ) ),
    inference(superposition,[],[f52,f315])).

fof(f315,plain,(
    ! [X0,X1] :
      ( sK6(sK5,k1_tarski(X0)) = X0
      | sP1(sK5,k1_tarski(X0))
      | ~ sP0(X1,sK5)
      | X0 != X1 ) ),
    inference(equality_factoring,[],[f292])).

fof(f292,plain,(
    ! [X2,X3] :
      ( sK6(sK5,k1_tarski(X2)) = X3
      | sP1(sK5,k1_tarski(X2))
      | ~ sP0(X3,sK5)
      | sK6(sK5,k1_tarski(X2)) = X2 ) ),
    inference(resolution,[],[f283,f109])).

% (6545)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f283,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK5,X0),X0)
      | sP1(sK5,X0)
      | sK6(sK5,X0) = X1
      | ~ sP0(X1,sK5) ) ),
    inference(resolution,[],[f51,f180])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP0(sK6(X0,X1),X0)
      | sP1(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK6(X0,X1),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sP0(sK6(X0,X1),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK6(X0,X1),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sP0(sK6(X0,X1),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK6(X0,X1),X0)
      | sP1(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f197,plain,(
    spl11_8 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl11_8 ),
    inference(subsumption_resolution,[],[f195,f43])).

fof(f43,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f195,plain,
    ( ~ v1_relat_1(sK5)
    | spl11_8 ),
    inference(subsumption_resolution,[],[f194,f44])).

fof(f44,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f194,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl11_8 ),
    inference(resolution,[],[f189,f56])).

fof(f56,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f12,f19,f18,f17])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f189,plain,
    ( ~ sP2(sK5)
    | spl11_8 ),
    inference(avatar_component_clause,[],[f187])).

fof(f161,plain,(
    ~ spl11_1 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl11_1 ),
    inference(resolution,[],[f156,f73])).

fof(f156,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_tarski(sK4))
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f155,f45])).

fof(f155,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ spl11_1 ),
    inference(resolution,[],[f97,f69])).

fof(f69,plain,(
    ! [X2,X1] :
      ( sP0(k1_funct_1(X1,X2),X1)
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | k1_funct_1(X1,X2) != X0
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,
    ( ! [X3] : ~ sP0(X3,sK5)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:15:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (6526)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.54  % (6526)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (6542)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f341,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f161,f197,f340])).
% 0.20/0.55  fof(f340,plain,(
% 0.20/0.55    spl11_1 | ~spl11_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f339,f187,f96])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    spl11_1 <=> ! [X3] : ~sP0(X3,sK5)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.20/0.55  fof(f187,plain,(
% 0.20/0.55    spl11_8 <=> sP2(sK5)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.20/0.55  fof(f339,plain,(
% 0.20/0.55    ( ! [X0] : (~sP0(X0,sK5)) ) | ~spl11_8),
% 0.20/0.55    inference(subsumption_resolution,[],[f338,f209])).
% 0.20/0.55  fof(f209,plain,(
% 0.20/0.55    ( ! [X0] : (~sP1(sK5,k1_tarski(X0)) | ~sP0(X0,sK5)) ) | ~spl11_8),
% 0.20/0.55    inference(resolution,[],[f208,f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X0] : (sP3(X0,k1_tarski(X0))) )),
% 0.20/0.55    inference(equality_resolution,[],[f64])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sP3(X0,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP3(X0,X1)) & (sP3(X0,X1) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP3(X0,X1))),
% 0.20/0.55    inference(definition_folding,[],[f1,f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.55  fof(f208,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~sP3(X1,X0) | ~sP0(X1,sK5) | ~sP1(sK5,X0)) ) | ~spl11_8),
% 0.20/0.55    inference(subsumption_resolution,[],[f207,f188])).
% 0.20/0.55  fof(f188,plain,(
% 0.20/0.55    sP2(sK5) | ~spl11_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f187])).
% 0.20/0.55  fof(f207,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~sP3(X1,X0) | ~sP0(X1,sK5) | ~sP1(sK5,X0) | ~sP2(sK5)) )),
% 0.20/0.55    inference(superposition,[],[f205,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | ~sP1(X0,X1) | ~sP2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.55  fof(f205,plain,(
% 0.20/0.55    ( ! [X0] : (~sP3(X0,k2_relat_1(sK5)) | ~sP0(X0,sK5)) )),
% 0.20/0.55    inference(equality_resolution,[],[f181])).
% 0.20/0.55  fof(f181,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_relat_1(sK5) != X1 | ~sP3(X0,X1) | ~sP0(X0,sK5)) )),
% 0.20/0.55    inference(superposition,[],[f75,f178])).
% 0.20/0.55  fof(f178,plain,(
% 0.20/0.55    ( ! [X2] : (k1_funct_1(sK5,sK4) = X2 | ~sP0(X2,sK5)) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f176])).
% 0.20/0.55  fof(f176,plain,(
% 0.20/0.55    ( ! [X2] : (k1_funct_1(sK5,sK4) = X2 | ~sP0(X2,sK5) | ~sP0(X2,sK5)) )),
% 0.20/0.55    inference(superposition,[],[f54,f114])).
% 0.20/0.56  fof(f114,plain,(
% 0.20/0.56    ( ! [X1] : (sK4 = sK7(X1,sK5) | ~sP0(X1,sK5)) )),
% 0.20/0.56    inference(resolution,[],[f109,f86])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK7(X0,sK5),k1_tarski(sK4)) | ~sP0(X0,sK5)) )),
% 0.20/0.56    inference(superposition,[],[f53,f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    k1_tarski(sK4) = k1_relat_1(sK5)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    k2_relat_1(sK5) != k1_tarski(k1_funct_1(sK5,sK4)) & k1_tarski(sK4) = k1_relat_1(sK5) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK5) != k1_tarski(k1_funct_1(sK5,sK4)) & k1_tarski(sK4) = k1_relat_1(sK5) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f10,plain,(
% 0.20/0.56    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.56    inference(flattening,[],[f9])).
% 0.20/0.56  fof(f9,plain,(
% 0.20/0.56    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.56    inference(negated_conjecture,[],[f7])).
% 0.20/0.56  fof(f7,conjecture,(
% 0.20/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),k1_relat_1(X1)) | ~sP0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK7(X0,X1)) = X0 & r2_hidden(sK7(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK7(X0,X1)) = X0 & r2_hidden(sK7(X0,X1),k1_relat_1(X1))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 0.20/0.56    inference(nnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.56  fof(f109,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 0.20/0.56    inference(resolution,[],[f60,f71])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~sP3(X0,X1) | ~r2_hidden(X3,X1) | X0 = X3) )),
% 0.20/0.56    inference(cnf_transformation,[],[f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ! [X0,X1] : ((sP3(X0,X1) | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP3(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f21])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_funct_1(X1,sK7(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f75,plain,(
% 0.20/0.56    ( ! [X0] : (~sP3(k1_funct_1(sK5,sK4),X0) | k2_relat_1(sK5) != X0) )),
% 0.20/0.56    inference(superposition,[],[f46,f65])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_tarski(X0) = X1 | ~sP3(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f40])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    k2_relat_1(sK5) != k1_tarski(k1_funct_1(sK5,sK4))),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f338,plain,(
% 0.20/0.56    ( ! [X0] : (~sP0(X0,sK5) | sP1(sK5,k1_tarski(X0))) )),
% 0.20/0.56    inference(condensation,[],[f337])).
% 0.20/0.56  fof(f337,plain,(
% 0.20/0.56    ( ! [X8,X9] : (~sP0(X8,sK5) | sP1(sK5,k1_tarski(X8)) | ~sP0(X9,sK5)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f336,f180])).
% 0.20/0.56  fof(f180,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~sP0(X1,sK5) | X0 = X1 | ~sP0(X0,sK5)) )),
% 0.20/0.56    inference(superposition,[],[f178,f178])).
% 0.20/0.56  fof(f336,plain,(
% 0.20/0.56    ( ! [X8,X9] : (~sP0(X8,sK5) | sP1(sK5,k1_tarski(X8)) | ~sP0(X9,sK5) | X8 != X9) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f331,f73])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.20/0.56    inference(resolution,[],[f70,f71])).
% 0.20/0.56  fof(f70,plain,(
% 0.20/0.56    ( ! [X3,X1] : (~sP3(X3,X1) | r2_hidden(X3,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | ~sP3(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f39])).
% 0.20/0.56  fof(f331,plain,(
% 0.20/0.56    ( ! [X8,X9] : (~sP0(X8,sK5) | sP1(sK5,k1_tarski(X8)) | ~r2_hidden(X8,k1_tarski(X8)) | ~sP0(X9,sK5) | X8 != X9) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f328])).
% 0.20/0.56  fof(f328,plain,(
% 0.20/0.56    ( ! [X8,X9] : (~sP0(X8,sK5) | sP1(sK5,k1_tarski(X8)) | ~r2_hidden(X8,k1_tarski(X8)) | sP1(sK5,k1_tarski(X8)) | ~sP0(X9,sK5) | X8 != X9) )),
% 0.20/0.56    inference(superposition,[],[f52,f315])).
% 0.20/0.56  fof(f315,plain,(
% 0.20/0.56    ( ! [X0,X1] : (sK6(sK5,k1_tarski(X0)) = X0 | sP1(sK5,k1_tarski(X0)) | ~sP0(X1,sK5) | X0 != X1) )),
% 0.20/0.56    inference(equality_factoring,[],[f292])).
% 0.20/0.56  fof(f292,plain,(
% 0.20/0.56    ( ! [X2,X3] : (sK6(sK5,k1_tarski(X2)) = X3 | sP1(sK5,k1_tarski(X2)) | ~sP0(X3,sK5) | sK6(sK5,k1_tarski(X2)) = X2) )),
% 0.20/0.56    inference(resolution,[],[f283,f109])).
% 0.20/0.56  % (6545)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.56  fof(f283,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK6(sK5,X0),X0) | sP1(sK5,X0) | sK6(sK5,X0) = X1 | ~sP0(X1,sK5)) )),
% 0.20/0.56    inference(resolution,[],[f51,f180])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0,X1] : (sP0(sK6(X0,X1),X0) | sP1(X0,X1) | r2_hidden(sK6(X0,X1),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (sP0(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (sP0(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~sP0(sK6(X0,X1),X0) | sP1(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f197,plain,(
% 0.20/0.56    spl11_8),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f196])).
% 0.20/0.56  fof(f196,plain,(
% 0.20/0.56    $false | spl11_8),
% 0.20/0.56    inference(subsumption_resolution,[],[f195,f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    v1_relat_1(sK5)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f195,plain,(
% 0.20/0.56    ~v1_relat_1(sK5) | spl11_8),
% 0.20/0.56    inference(subsumption_resolution,[],[f194,f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    v1_funct_1(sK5)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f194,plain,(
% 0.20/0.56    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl11_8),
% 0.20/0.56    inference(resolution,[],[f189,f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(definition_folding,[],[f12,f19,f18,f17])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f11])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.56  fof(f189,plain,(
% 0.20/0.56    ~sP2(sK5) | spl11_8),
% 0.20/0.56    inference(avatar_component_clause,[],[f187])).
% 0.20/0.56  fof(f161,plain,(
% 0.20/0.56    ~spl11_1),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.56  fof(f158,plain,(
% 0.20/0.56    $false | ~spl11_1),
% 0.20/0.56    inference(resolution,[],[f156,f73])).
% 0.20/0.56  fof(f156,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK4))) ) | ~spl11_1),
% 0.20/0.56    inference(forward_demodulation,[],[f155,f45])).
% 0.20/0.56  fof(f155,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK5))) ) | ~spl11_1),
% 0.20/0.56    inference(resolution,[],[f97,f69])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    ( ! [X2,X1] : (sP0(k1_funct_1(X1,X2),X1) | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 0.20/0.56    inference(equality_resolution,[],[f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (sP0(X0,X1) | k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    ( ! [X3] : (~sP0(X3,sK5)) ) | ~spl11_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f96])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (6526)------------------------------
% 0.20/0.56  % (6526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (6526)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (6526)Memory used [KB]: 6268
% 0.20/0.56  % (6526)Time elapsed: 0.102 s
% 0.20/0.56  % (6526)------------------------------
% 0.20/0.56  % (6526)------------------------------
% 0.20/0.56  % (6521)Success in time 0.197 s
%------------------------------------------------------------------------------
