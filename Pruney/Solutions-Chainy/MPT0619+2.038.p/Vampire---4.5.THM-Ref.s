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
fof(f306,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f161,f242,f305])).

fof(f305,plain,
    ( spl10_1
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f304,f151,f105])).

fof(f105,plain,
    ( spl10_1
  <=> ! [X0] : ~ sP0(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f151,plain,
    ( spl10_6
  <=> sP2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f304,plain,
    ( ! [X0] : ~ sP0(X0,sK5)
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f303,f169])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ sP1(sK5,k1_tarski(X0))
        | ~ sP0(X0,sK5) )
    | ~ spl10_6 ),
    inference(resolution,[],[f168,f64])).

fof(f64,plain,(
    ! [X0] : sP3(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP3(X0,X1) )
      & ( sP3(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP3(X0,X1) ) ),
    inference(definition_folding,[],[f1,f18])).

fof(f18,plain,(
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

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X1,X0)
        | ~ sP0(X1,sK5)
        | ~ sP1(sK5,X0) )
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f167,f152])).

fof(f152,plain,
    ( sP2(sK5)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ sP3(X1,X0)
      | ~ sP0(X1,sK5)
      | ~ sP1(sK5,X0)
      | ~ sP2(sK5) ) ),
    inference(superposition,[],[f165,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | ~ sP1(X0,X1)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f165,plain,(
    ! [X0] :
      ( ~ sP3(X0,k2_relat_1(sK5))
      | ~ sP0(X0,sK5) ) ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK5) != X1
      | ~ sP3(X0,X1)
      | ~ sP0(X0,sK5) ) ),
    inference(superposition,[],[f68,f142])).

fof(f142,plain,(
    ! [X2] :
      ( k1_funct_1(sK5,sK4) = X2
      | ~ sP0(X2,sK5) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X2] :
      ( k1_funct_1(sK5,sK4) = X2
      | ~ sP0(X2,sK5)
      | ~ sP0(X2,sK5) ) ),
    inference(superposition,[],[f49,f82])).

fof(f82,plain,(
    ! [X1] :
      ( sK4 = sK7(X1,sK5)
      | ~ sP0(X1,sK5) ) ),
    inference(resolution,[],[f79,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0,sK5),k1_tarski(sK4))
      | ~ sP0(X0,sK5) ) ),
    inference(superposition,[],[f48,f40])).

fof(f40,plain,(
    k1_tarski(sK4) = k1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k2_relat_1(sK5) != k1_tarski(k1_funct_1(sK5,sK4))
    & k1_tarski(sK4) = k1_relat_1(sK5)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f8,f20])).

fof(f20,plain,
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

fof(f8,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK7(X0,X1)) = X0
          & r2_hidden(sK7(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK7(X0,X1)) = X0
        & r2_hidden(sK7(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f53,f64])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ( sK8(X0,X1) != X0
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( sK8(X0,X1) = X0
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK8(X0,X1) != X0
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( sK8(X0,X1) = X0
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK7(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X0] :
      ( ~ sP3(k1_funct_1(sK5,sK4),X0)
      | k2_relat_1(sK5) != X0 ) ),
    inference(superposition,[],[f41,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f41,plain,(
    k2_relat_1(sK5) != k1_tarski(k1_funct_1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f303,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK5)
      | sP1(sK5,k1_tarski(X0)) ) ),
    inference(condensation,[],[f302])).

fof(f302,plain,(
    ! [X6,X5] :
      ( ~ sP0(X5,sK5)
      | sP1(sK5,k1_tarski(X5))
      | ~ sP0(X6,sK5) ) ),
    inference(subsumption_resolution,[],[f301,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,sK5)
      | X0 = X1
      | ~ sP0(X0,sK5) ) ),
    inference(superposition,[],[f142,f142])).

fof(f301,plain,(
    ! [X6,X5] :
      ( ~ sP0(X5,sK5)
      | sP1(sK5,k1_tarski(X5))
      | ~ sP0(X6,sK5)
      | X5 != X6 ) ),
    inference(subsumption_resolution,[],[f298,f66])).

fof(f66,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f63,f64])).

fof(f63,plain,(
    ! [X3,X1] :
      ( ~ sP3(X3,X1)
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f298,plain,(
    ! [X6,X5] :
      ( ~ sP0(X5,sK5)
      | sP1(sK5,k1_tarski(X5))
      | ~ r2_hidden(X5,k1_tarski(X5))
      | ~ sP0(X6,sK5)
      | X5 != X6 ) ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,(
    ! [X6,X5] :
      ( ~ sP0(X5,sK5)
      | sP1(sK5,k1_tarski(X5))
      | ~ r2_hidden(X5,k1_tarski(X5))
      | sP1(sK5,k1_tarski(X5))
      | ~ sP0(X6,sK5)
      | X5 != X6 ) ),
    inference(superposition,[],[f47,f286])).

fof(f286,plain,(
    ! [X0,X1] :
      ( sK6(sK5,k1_tarski(X0)) = X0
      | sP1(sK5,k1_tarski(X0))
      | ~ sP0(X1,sK5)
      | X0 != X1 ) ),
    inference(equality_factoring,[],[f275])).

fof(f275,plain,(
    ! [X0,X1] :
      ( sK6(sK5,k1_tarski(X0)) = X1
      | sP1(sK5,k1_tarski(X0))
      | ~ sP0(X1,sK5)
      | sK6(sK5,k1_tarski(X0)) = X0 ) ),
    inference(resolution,[],[f232,f79])).

fof(f232,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK6(sK5,X1),X1)
      | sP1(sK5,X1)
      | sK6(sK5,X1) = X2
      | ~ sP0(X2,sK5) ) ),
    inference(resolution,[],[f46,f144])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP0(sK6(X0,X1),X0)
      | sP1(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
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

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK6(X0,X1),X0)
      | sP1(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f242,plain,(
    ~ spl10_1 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl10_1 ),
    inference(resolution,[],[f230,f66])).

fof(f230,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_tarski(sK4))
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f228,f40])).

fof(f228,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ spl10_1 ),
    inference(resolution,[],[f106,f62])).

fof(f62,plain,(
    ! [X2,X1] :
      ( sP0(k1_funct_1(X1,X2),X1)
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | k1_funct_1(X1,X2) != X0
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,
    ( ! [X0] : ~ sP0(X0,sK5)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f161,plain,(
    spl10_6 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl10_6 ),
    inference(subsumption_resolution,[],[f159,f38])).

fof(f38,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f159,plain,
    ( ~ v1_relat_1(sK5)
    | spl10_6 ),
    inference(subsumption_resolution,[],[f158,f39])).

fof(f39,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f158,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl10_6 ),
    inference(resolution,[],[f153,f51])).

fof(f51,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f16,f15,f14])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f153,plain,
    ( ~ sP2(sK5)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:14:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (17919)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.47  % (17919)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (17927)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (17937)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f306,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f161,f242,f305])).
% 0.20/0.48  fof(f305,plain,(
% 0.20/0.48    spl10_1 | ~spl10_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f304,f151,f105])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    spl10_1 <=> ! [X0] : ~sP0(X0,sK5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    spl10_6 <=> sP2(sK5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.48  fof(f304,plain,(
% 0.20/0.48    ( ! [X0] : (~sP0(X0,sK5)) ) | ~spl10_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f303,f169])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ( ! [X0] : (~sP1(sK5,k1_tarski(X0)) | ~sP0(X0,sK5)) ) | ~spl10_6),
% 0.20/0.48    inference(resolution,[],[f168,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0] : (sP3(X0,k1_tarski(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP3(X0,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP3(X0,X1)) & (sP3(X0,X1) | k1_tarski(X0) != X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP3(X0,X1))),
% 0.20/0.48    inference(definition_folding,[],[f1,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~sP3(X1,X0) | ~sP0(X1,sK5) | ~sP1(sK5,X0)) ) | ~spl10_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f167,f152])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    sP2(sK5) | ~spl10_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f151])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~sP3(X1,X0) | ~sP0(X1,sK5) | ~sP1(sK5,X0) | ~sP2(sK5)) )),
% 0.20/0.48    inference(superposition,[],[f165,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | ~sP1(X0,X1) | ~sP2(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    ( ! [X0] : (~sP3(X0,k2_relat_1(sK5)) | ~sP0(X0,sK5)) )),
% 0.20/0.48    inference(equality_resolution,[],[f145])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_relat_1(sK5) != X1 | ~sP3(X0,X1) | ~sP0(X0,sK5)) )),
% 0.20/0.48    inference(superposition,[],[f68,f142])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    ( ! [X2] : (k1_funct_1(sK5,sK4) = X2 | ~sP0(X2,sK5)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f140])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ( ! [X2] : (k1_funct_1(sK5,sK4) = X2 | ~sP0(X2,sK5) | ~sP0(X2,sK5)) )),
% 0.20/0.48    inference(superposition,[],[f49,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X1] : (sK4 = sK7(X1,sK5) | ~sP0(X1,sK5)) )),
% 0.20/0.48    inference(resolution,[],[f79,f78])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK7(X0,sK5),k1_tarski(sK4)) | ~sP0(X0,sK5)) )),
% 0.20/0.48    inference(superposition,[],[f48,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    k1_tarski(sK4) = k1_relat_1(sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    k2_relat_1(sK5) != k1_tarski(k1_funct_1(sK5,sK4)) & k1_tarski(sK4) = k1_relat_1(sK5) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f8,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK5) != k1_tarski(k1_funct_1(sK5,sK4)) & k1_tarski(sK4) = k1_relat_1(sK5) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),k1_relat_1(X1)) | ~sP0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK7(X0,X1)) = X0 & r2_hidden(sK7(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK7(X0,X1)) = X0 & r2_hidden(sK7(X0,X1),k1_relat_1(X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 0.20/0.48    inference(resolution,[],[f53,f64])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~sP3(X0,X1) | ~r2_hidden(X3,X1) | X0 = X3) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP3(X0,X1) | ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP3(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f18])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_funct_1(X1,sK7(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X0] : (~sP3(k1_funct_1(sK5,sK4),X0) | k2_relat_1(sK5) != X0) )),
% 0.20/0.48    inference(superposition,[],[f41,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_tarski(X0) = X1 | ~sP3(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    k2_relat_1(sK5) != k1_tarski(k1_funct_1(sK5,sK4))),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f303,plain,(
% 0.20/0.48    ( ! [X0] : (~sP0(X0,sK5) | sP1(sK5,k1_tarski(X0))) )),
% 0.20/0.48    inference(condensation,[],[f302])).
% 0.20/0.48  fof(f302,plain,(
% 0.20/0.48    ( ! [X6,X5] : (~sP0(X5,sK5) | sP1(sK5,k1_tarski(X5)) | ~sP0(X6,sK5)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f301,f144])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~sP0(X1,sK5) | X0 = X1 | ~sP0(X0,sK5)) )),
% 0.20/0.48    inference(superposition,[],[f142,f142])).
% 0.20/0.48  fof(f301,plain,(
% 0.20/0.48    ( ! [X6,X5] : (~sP0(X5,sK5) | sP1(sK5,k1_tarski(X5)) | ~sP0(X6,sK5) | X5 != X6) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f298,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.20/0.48    inference(resolution,[],[f63,f64])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X3,X1] : (~sP3(X3,X1) | r2_hidden(X3,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | ~sP3(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f298,plain,(
% 0.20/0.48    ( ! [X6,X5] : (~sP0(X5,sK5) | sP1(sK5,k1_tarski(X5)) | ~r2_hidden(X5,k1_tarski(X5)) | ~sP0(X6,sK5) | X5 != X6) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f295])).
% 0.20/0.48  fof(f295,plain,(
% 0.20/0.48    ( ! [X6,X5] : (~sP0(X5,sK5) | sP1(sK5,k1_tarski(X5)) | ~r2_hidden(X5,k1_tarski(X5)) | sP1(sK5,k1_tarski(X5)) | ~sP0(X6,sK5) | X5 != X6) )),
% 0.20/0.48    inference(superposition,[],[f47,f286])).
% 0.20/0.48  fof(f286,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sK6(sK5,k1_tarski(X0)) = X0 | sP1(sK5,k1_tarski(X0)) | ~sP0(X1,sK5) | X0 != X1) )),
% 0.20/0.48    inference(equality_factoring,[],[f275])).
% 0.20/0.48  fof(f275,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sK6(sK5,k1_tarski(X0)) = X1 | sP1(sK5,k1_tarski(X0)) | ~sP0(X1,sK5) | sK6(sK5,k1_tarski(X0)) = X0) )),
% 0.20/0.48    inference(resolution,[],[f232,f79])).
% 0.20/0.48  fof(f232,plain,(
% 0.20/0.48    ( ! [X2,X1] : (r2_hidden(sK6(sK5,X1),X1) | sP1(sK5,X1) | sK6(sK5,X1) = X2 | ~sP0(X2,sK5)) )),
% 0.20/0.48    inference(resolution,[],[f46,f144])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP0(sK6(X0,X1),X0) | sP1(X0,X1) | r2_hidden(sK6(X0,X1),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (sP0(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (sP0(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~sP0(sK6(X0,X1),X0) | sP1(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f242,plain,(
% 0.20/0.48    ~spl10_1),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f238])).
% 0.20/0.48  fof(f238,plain,(
% 0.20/0.48    $false | ~spl10_1),
% 0.20/0.48    inference(resolution,[],[f230,f66])).
% 0.20/0.48  fof(f230,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK4))) ) | ~spl10_1),
% 0.20/0.48    inference(forward_demodulation,[],[f228,f40])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK5))) ) | ~spl10_1),
% 0.20/0.48    inference(resolution,[],[f106,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X2,X1] : (sP0(k1_funct_1(X1,X2),X1) | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 0.20/0.48    inference(equality_resolution,[],[f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP0(X0,X1) | k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ( ! [X0] : (~sP0(X0,sK5)) ) | ~spl10_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f105])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    spl10_6),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f160])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    $false | spl10_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f159,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    v1_relat_1(sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    ~v1_relat_1(sK5) | spl10_6),
% 0.20/0.48    inference(subsumption_resolution,[],[f158,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v1_funct_1(sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl10_6),
% 0.20/0.48    inference(resolution,[],[f153,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(definition_folding,[],[f10,f16,f15,f14])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    ~sP2(sK5) | spl10_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f151])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (17919)------------------------------
% 0.20/0.48  % (17919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17919)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (17919)Memory used [KB]: 6268
% 0.20/0.48  % (17919)Time elapsed: 0.061 s
% 0.20/0.48  % (17919)------------------------------
% 0.20/0.48  % (17919)------------------------------
% 0.20/0.48  % (17914)Success in time 0.126 s
%------------------------------------------------------------------------------
