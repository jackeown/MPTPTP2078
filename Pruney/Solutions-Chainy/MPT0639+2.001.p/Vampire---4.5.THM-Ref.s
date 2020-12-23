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
% DateTime   : Thu Dec  3 12:52:37 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 654 expanded)
%              Number of leaves         :   22 ( 210 expanded)
%              Depth                    :   22
%              Number of atoms          :  658 (3917 expanded)
%              Number of equality atoms :   69 ( 209 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f171,f196,f202,f244,f266,f293,f299,f336,f387,f491])).

fof(f491,plain,
    ( ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f489,f45])).

fof(f45,plain,(
    ~ v2_funct_1(k5_relat_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v2_funct_1(k5_relat_1(sK4,sK5))
    & v2_funct_1(sK5)
    & v2_funct_1(sK4)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f9,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_funct_1(k5_relat_1(X0,X1))
            & v2_funct_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(sK4,X1))
          & v2_funct_1(X1)
          & v2_funct_1(sK4)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ v2_funct_1(k5_relat_1(sK4,X1))
        & v2_funct_1(X1)
        & v2_funct_1(sK4)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(k5_relat_1(sK4,sK5))
      & v2_funct_1(sK5)
      & v2_funct_1(sK4)
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( v2_funct_1(X1)
                & v2_funct_1(X0) )
             => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

fof(f489,plain,
    ( v2_funct_1(k5_relat_1(sK4,sK5))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f488,f41])).

fof(f41,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f488,plain,
    ( ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f487,f42])).

fof(f42,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f487,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f486,f39])).

fof(f39,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f486,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f485,f40])).

fof(f40,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f485,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(resolution,[],[f478,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ sP0(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k5_relat_1(X1,X0)) ) ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f75,plain,(
    ! [X0,X1] :
      ( sP1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f74,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sP1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(resolution,[],[f55,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f11,f21,f20])).

fof(f20,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f478,plain,
    ( sP0(k5_relat_1(sK4,sK5))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(trivial_inequality_removal,[],[f476])).

fof(f476,plain,
    ( sK6(k5_relat_1(sK4,sK5)) != sK6(k5_relat_1(sK4,sK5))
    | sP0(k5_relat_1(sK4,sK5))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(superposition,[],[f52,f441])).

fof(f441,plain,
    ( sK6(k5_relat_1(sK4,sK5)) = sK7(k5_relat_1(sK4,sK5))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f440,f205])).

fof(f205,plain,
    ( r2_hidden(sK6(k5_relat_1(sK4,sK5)),k1_relat_1(sK4))
    | ~ spl8_4 ),
    inference(resolution,[],[f195,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0))
        | ~ r2_hidden(X1,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X2)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
        & r2_hidden(X0,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f195,plain,
    ( sP2(sK5,sK6(k5_relat_1(sK4,sK5)),sK4)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl8_4
  <=> sP2(sK5,sK6(k5_relat_1(sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f440,plain,
    ( sK6(k5_relat_1(sK4,sK5)) = sK7(k5_relat_1(sK4,sK5))
    | ~ r2_hidden(sK6(k5_relat_1(sK4,sK5)),k1_relat_1(sK4))
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(equality_resolution,[],[f419])).

fof(f419,plain,
    ( ! [X0] :
        ( k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))) != k1_funct_1(sK4,X0)
        | sK7(k5_relat_1(sK4,sK5)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK4)) )
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f418,f70])).

fof(f70,plain,(
    sP0(sK4) ),
    inference(subsumption_resolution,[],[f69,f43])).

fof(f43,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,
    ( ~ v2_funct_1(sK4)
    | sP0(sK4) ),
    inference(resolution,[],[f66,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_funct_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    sP1(sK4) ),
    inference(subsumption_resolution,[],[f64,f39])).

fof(f64,plain,
    ( sP1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f53,f40])).

fof(f418,plain,
    ( ! [X0] :
        ( k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))) != k1_funct_1(sK4,X0)
        | sK7(k5_relat_1(sK4,sK5)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | ~ sP0(sK4) )
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f411,f302])).

fof(f302,plain,
    ( r2_hidden(sK7(k5_relat_1(sK4,sK5)),k1_relat_1(sK4))
    | ~ spl8_11 ),
    inference(resolution,[],[f292,f59])).

fof(f292,plain,
    ( sP2(sK5,sK7(k5_relat_1(sK4,sK5)),sK4)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl8_11
  <=> sP2(sK5,sK7(k5_relat_1(sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f411,plain,
    ( ! [X0] :
        ( k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))) != k1_funct_1(sK4,X0)
        | sK7(k5_relat_1(sK4,sK5)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | ~ r2_hidden(sK7(k5_relat_1(sK4,sK5)),k1_relat_1(sK4))
        | ~ sP0(sK4) )
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(superposition,[],[f48,f390])).

fof(f390,plain,
    ( k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5)))
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f389,f236])).

fof(f236,plain,
    ( r2_hidden(k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))),k1_relat_1(sK5))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl8_5
  <=> r2_hidden(k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f389,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))),k1_relat_1(sK5))
    | k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5)))
    | ~ spl8_16 ),
    inference(equality_resolution,[],[f386])).

fof(f386,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) != k1_funct_1(sK5,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK5))
        | k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))) = X0 )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl8_16
  <=> ! [X0] :
        ( k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) != k1_funct_1(sK5,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK5))
        | k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f48,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK6(X0) != sK7(X0)
          & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
          & r2_hidden(sK7(X0),k1_relat_1(X0))
          & r2_hidden(sK6(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK6(X0) != sK7(X0)
        & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
        & r2_hidden(sK7(X0),k1_relat_1(X0))
        & r2_hidden(sK6(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0] :
      ( sK6(X0) != sK7(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f387,plain,
    ( ~ spl8_12
    | spl8_16
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f315,f251,f145,f385,f327])).

fof(f327,plain,
    ( spl8_12
  <=> r2_hidden(k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f145,plain,
    ( spl8_1
  <=> r2_hidden(sK6(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f251,plain,
    ( spl8_8
  <=> r2_hidden(sK7(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f315,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) != k1_funct_1(sK5,X0)
        | k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK5))
        | ~ r2_hidden(k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))),k1_relat_1(sK5)) )
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f308,f73])).

fof(f73,plain,(
    sP0(sK5) ),
    inference(subsumption_resolution,[],[f72,f44])).

fof(f44,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,
    ( ~ v2_funct_1(sK5)
    | sP0(sK5) ),
    inference(resolution,[],[f67,f46])).

fof(f67,plain,(
    sP1(sK5) ),
    inference(subsumption_resolution,[],[f65,f41])).

fof(f65,plain,
    ( sP1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f53,f42])).

fof(f308,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) != k1_funct_1(sK5,X0)
        | k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK5))
        | ~ r2_hidden(k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))),k1_relat_1(sK5))
        | ~ sP0(sK5) )
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(superposition,[],[f48,f273])).

fof(f273,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))))
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f272,f178])).

fof(f178,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f133,f177])).

fof(f177,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f176,f41])).

fof(f176,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))))
    | ~ v1_relat_1(sK5)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f175,f42])).

fof(f175,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f174,f39])).

fof(f174,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f172,f40])).

fof(f172,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl8_1 ),
    inference(resolution,[],[f146,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f146,plain,
    ( r2_hidden(sK6(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f145])).

fof(f133,plain,(
    k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f132,f40])).

fof(f132,plain,
    ( ~ v1_funct_1(sK4)
    | k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f131,f41])).

fof(f131,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f130,f42])).

fof(f130,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f127,f39])).

fof(f127,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) ),
    inference(resolution,[],[f85,f45])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | k1_funct_1(k5_relat_1(X0,X1),sK6(k5_relat_1(X0,X1))) = k1_funct_1(k5_relat_1(X0,X1),sK7(k5_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f76,f51])).

fof(f51,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f272,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))))
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f271,f41])).

fof(f271,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))))
    | ~ v1_relat_1(sK5)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f270,f42])).

fof(f270,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f269,f39])).

fof(f269,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f267,f40])).

fof(f267,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl8_8 ),
    inference(resolution,[],[f252,f56])).

fof(f252,plain,
    ( r2_hidden(sK7(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f251])).

fof(f336,plain,
    ( ~ spl8_11
    | spl8_12 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl8_11
    | spl8_12 ),
    inference(subsumption_resolution,[],[f334,f292])).

fof(f334,plain,
    ( ~ sP2(sK5,sK7(k5_relat_1(sK4,sK5)),sK4)
    | spl8_12 ),
    inference(resolution,[],[f329,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f329,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))),k1_relat_1(sK5))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f327])).

fof(f299,plain,(
    spl8_10 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl8_10 ),
    inference(subsumption_resolution,[],[f297,f41])).

fof(f297,plain,
    ( ~ v1_relat_1(sK5)
    | spl8_10 ),
    inference(subsumption_resolution,[],[f296,f42])).

fof(f296,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl8_10 ),
    inference(subsumption_resolution,[],[f295,f39])).

fof(f295,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl8_10 ),
    inference(subsumption_resolution,[],[f294,f40])).

fof(f294,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl8_10 ),
    inference(resolution,[],[f288,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP3(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f17,f24,f23])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      <=> sP2(X1,X0,X2) )
      | ~ sP3(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f288,plain,
    ( ~ sP3(sK4,sK7(k5_relat_1(sK4,sK5)),sK5)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl8_10
  <=> sP3(sK4,sK7(k5_relat_1(sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f293,plain,
    ( ~ spl8_10
    | spl8_11
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f268,f251,f290,f286])).

fof(f268,plain,
    ( sP2(sK5,sK7(k5_relat_1(sK4,sK5)),sK4)
    | ~ sP3(sK4,sK7(k5_relat_1(sK4,sK5)),sK5)
    | ~ spl8_8 ),
    inference(resolution,[],[f252,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2)))
      | sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2)))
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2))) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ sP2(X1,X0,X2) )
        & ( sP2(X1,X0,X2)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
      | ~ sP3(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f266,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl8_8 ),
    inference(subsumption_resolution,[],[f264,f45])).

fof(f264,plain,
    ( v2_funct_1(k5_relat_1(sK4,sK5))
    | spl8_8 ),
    inference(subsumption_resolution,[],[f263,f41])).

fof(f263,plain,
    ( ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | spl8_8 ),
    inference(subsumption_resolution,[],[f262,f42])).

fof(f262,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | spl8_8 ),
    inference(subsumption_resolution,[],[f261,f39])).

fof(f261,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | spl8_8 ),
    inference(subsumption_resolution,[],[f260,f40])).

fof(f260,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | spl8_8 ),
    inference(resolution,[],[f259,f76])).

fof(f259,plain,
    ( sP0(k5_relat_1(sK4,sK5))
    | spl8_8 ),
    inference(resolution,[],[f253,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f253,plain,
    ( ~ r2_hidden(sK7(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5)))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f251])).

fof(f244,plain,
    ( ~ spl8_4
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl8_4
    | spl8_5 ),
    inference(subsumption_resolution,[],[f242,f195])).

fof(f242,plain,
    ( ~ sP2(sK5,sK6(k5_relat_1(sK4,sK5)),sK4)
    | spl8_5 ),
    inference(resolution,[],[f237,f60])).

fof(f237,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))),k1_relat_1(sK5))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f235])).

fof(f202,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f200,f41])).

fof(f200,plain,
    ( ~ v1_relat_1(sK5)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f199,f42])).

fof(f199,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f198,f39])).

fof(f198,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f197,f40])).

fof(f197,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl8_3 ),
    inference(resolution,[],[f191,f62])).

fof(f191,plain,
    ( ~ sP3(sK4,sK6(k5_relat_1(sK4,sK5)),sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl8_3
  <=> sP3(sK4,sK6(k5_relat_1(sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f196,plain,
    ( ~ spl8_3
    | spl8_4
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f173,f145,f193,f189])).

fof(f173,plain,
    ( sP2(sK5,sK6(k5_relat_1(sK4,sK5)),sK4)
    | ~ sP3(sK4,sK6(k5_relat_1(sK4,sK5)),sK5)
    | ~ spl8_1 ),
    inference(resolution,[],[f146,f57])).

fof(f171,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f169,f45])).

fof(f169,plain,
    ( v2_funct_1(k5_relat_1(sK4,sK5))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f168,f41])).

fof(f168,plain,
    ( ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f167,f42])).

fof(f167,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f166,f39])).

fof(f166,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f165,f40])).

fof(f165,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | v2_funct_1(k5_relat_1(sK4,sK5))
    | spl8_1 ),
    inference(resolution,[],[f153,f76])).

fof(f153,plain,
    ( sP0(k5_relat_1(sK4,sK5))
    | spl8_1 ),
    inference(resolution,[],[f147,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f147,plain,
    ( ~ r2_hidden(sK6(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:48:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (21602)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.47  % (21597)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (21588)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (21585)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (21585)Refutation not found, incomplete strategy% (21585)------------------------------
% 0.22/0.51  % (21585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21585)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21585)Memory used [KB]: 10618
% 0.22/0.51  % (21585)Time elapsed: 0.094 s
% 0.22/0.51  % (21585)------------------------------
% 0.22/0.51  % (21585)------------------------------
% 0.22/0.52  % (21584)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (21595)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (21589)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (21587)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (21608)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (21590)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (21598)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (21591)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (21594)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (21606)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (21586)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (21593)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (21607)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (21603)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (21599)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (21596)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (21601)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.54  % (21609)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.54  % (21600)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.46/0.55  % (21605)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.46/0.55  % (21592)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.46/0.55  % (21604)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.58/0.57  % (21609)Refutation found. Thanks to Tanya!
% 1.58/0.57  % SZS status Theorem for theBenchmark
% 1.58/0.57  % SZS output start Proof for theBenchmark
% 1.58/0.57  fof(f492,plain,(
% 1.58/0.57    $false),
% 1.58/0.57    inference(avatar_sat_refutation,[],[f171,f196,f202,f244,f266,f293,f299,f336,f387,f491])).
% 1.58/0.57  fof(f491,plain,(
% 1.58/0.57    ~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_16),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f490])).
% 1.58/0.57  fof(f490,plain,(
% 1.58/0.57    $false | (~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(subsumption_resolution,[],[f489,f45])).
% 1.58/0.57  fof(f45,plain,(
% 1.58/0.57    ~v2_funct_1(k5_relat_1(sK4,sK5))),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f28,plain,(
% 1.58/0.57    (~v2_funct_1(k5_relat_1(sK4,sK5)) & v2_funct_1(sK5) & v2_funct_1(sK4) & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f9,f27,f26])).
% 1.58/0.57  fof(f26,plain,(
% 1.58/0.57    ? [X0] : (? [X1] : (~v2_funct_1(k5_relat_1(X0,X1)) & v2_funct_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~v2_funct_1(k5_relat_1(sK4,X1)) & v2_funct_1(X1) & v2_funct_1(sK4) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f27,plain,(
% 1.58/0.57    ? [X1] : (~v2_funct_1(k5_relat_1(sK4,X1)) & v2_funct_1(X1) & v2_funct_1(sK4) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v2_funct_1(k5_relat_1(sK4,sK5)) & v2_funct_1(sK5) & v2_funct_1(sK4) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f9,plain,(
% 1.58/0.57    ? [X0] : (? [X1] : (~v2_funct_1(k5_relat_1(X0,X1)) & v2_funct_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.58/0.57    inference(flattening,[],[f8])).
% 1.58/0.57  fof(f8,plain,(
% 1.58/0.57    ? [X0] : (? [X1] : ((~v2_funct_1(k5_relat_1(X0,X1)) & (v2_funct_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f7])).
% 1.58/0.57  fof(f7,negated_conjecture,(
% 1.58/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 1.58/0.57    inference(negated_conjecture,[],[f6])).
% 1.58/0.57  fof(f6,conjecture,(
% 1.58/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).
% 1.58/0.57  fof(f489,plain,(
% 1.58/0.57    v2_funct_1(k5_relat_1(sK4,sK5)) | (~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(subsumption_resolution,[],[f488,f41])).
% 1.58/0.57  fof(f41,plain,(
% 1.58/0.57    v1_relat_1(sK5)),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f488,plain,(
% 1.58/0.57    ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | (~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(subsumption_resolution,[],[f487,f42])).
% 1.58/0.57  fof(f42,plain,(
% 1.58/0.57    v1_funct_1(sK5)),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f487,plain,(
% 1.58/0.57    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | (~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(subsumption_resolution,[],[f486,f39])).
% 1.58/0.57  fof(f39,plain,(
% 1.58/0.57    v1_relat_1(sK4)),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f486,plain,(
% 1.58/0.57    ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | (~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(subsumption_resolution,[],[f485,f40])).
% 1.58/0.57  fof(f40,plain,(
% 1.58/0.57    v1_funct_1(sK4)),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f485,plain,(
% 1.58/0.57    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | (~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(resolution,[],[f478,f76])).
% 1.58/0.57  fof(f76,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~sP0(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k5_relat_1(X1,X0))) )),
% 1.58/0.57    inference(resolution,[],[f75,f47])).
% 1.58/0.57  fof(f47,plain,(
% 1.58/0.57    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f29])).
% 1.58/0.57  fof(f29,plain,(
% 1.58/0.57    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 1.58/0.57    inference(nnf_transformation,[],[f21])).
% 1.58/0.57  fof(f21,plain,(
% 1.58/0.57    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 1.58/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.58/0.57  fof(f75,plain,(
% 1.58/0.57    ( ! [X0,X1] : (sP1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f74,f63])).
% 1.58/0.57  fof(f63,plain,(
% 1.58/0.57    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f19])).
% 1.58/0.57  fof(f19,plain,(
% 1.58/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.58/0.57    inference(flattening,[],[f18])).
% 1.58/0.57  fof(f18,plain,(
% 1.58/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f1])).
% 1.58/0.57  fof(f1,axiom,(
% 1.58/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.58/0.57  fof(f74,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | sP1(k5_relat_1(X1,X0)) | ~v1_relat_1(k5_relat_1(X1,X0))) )),
% 1.58/0.57    inference(resolution,[],[f55,f53])).
% 1.58/0.57  fof(f53,plain,(
% 1.58/0.57    ( ! [X0] : (~v1_funct_1(X0) | sP1(X0) | ~v1_relat_1(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f22])).
% 1.58/0.57  fof(f22,plain,(
% 1.58/0.57    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.58/0.57    inference(definition_folding,[],[f11,f21,f20])).
% 1.58/0.57  fof(f20,plain,(
% 1.58/0.57    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 1.58/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.58/0.57  fof(f11,plain,(
% 1.58/0.57    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.58/0.57    inference(flattening,[],[f10])).
% 1.58/0.57  fof(f10,plain,(
% 1.58/0.57    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f2])).
% 1.58/0.57  fof(f2,axiom,(
% 1.58/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 1.58/0.57  fof(f55,plain,(
% 1.58/0.57    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f13])).
% 1.58/0.57  fof(f13,plain,(
% 1.58/0.57    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.58/0.57    inference(flattening,[],[f12])).
% 1.58/0.57  fof(f12,plain,(
% 1.58/0.57    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f3])).
% 1.58/0.57  fof(f3,axiom,(
% 1.58/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 1.58/0.57  fof(f478,plain,(
% 1.58/0.57    sP0(k5_relat_1(sK4,sK5)) | (~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(trivial_inequality_removal,[],[f476])).
% 1.58/0.57  fof(f476,plain,(
% 1.58/0.57    sK6(k5_relat_1(sK4,sK5)) != sK6(k5_relat_1(sK4,sK5)) | sP0(k5_relat_1(sK4,sK5)) | (~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(superposition,[],[f52,f441])).
% 1.58/0.57  fof(f441,plain,(
% 1.58/0.57    sK6(k5_relat_1(sK4,sK5)) = sK7(k5_relat_1(sK4,sK5)) | (~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(subsumption_resolution,[],[f440,f205])).
% 1.58/0.57  fof(f205,plain,(
% 1.58/0.57    r2_hidden(sK6(k5_relat_1(sK4,sK5)),k1_relat_1(sK4)) | ~spl8_4),
% 1.58/0.57    inference(resolution,[],[f195,f59])).
% 1.58/0.57  fof(f59,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X1,k1_relat_1(X2))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f38])).
% 1.58/0.57  fof(f38,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X2))) | ~sP2(X0,X1,X2)))),
% 1.58/0.57    inference(rectify,[],[f37])).
% 1.58/0.57  fof(f37,plain,(
% 1.58/0.57    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~sP2(X1,X0,X2)))),
% 1.58/0.57    inference(flattening,[],[f36])).
% 1.58/0.57  fof(f36,plain,(
% 1.58/0.57    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~sP2(X1,X0,X2)))),
% 1.58/0.57    inference(nnf_transformation,[],[f23])).
% 1.58/0.57  fof(f23,plain,(
% 1.58/0.57    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))),
% 1.58/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.58/0.57  fof(f195,plain,(
% 1.58/0.57    sP2(sK5,sK6(k5_relat_1(sK4,sK5)),sK4) | ~spl8_4),
% 1.58/0.57    inference(avatar_component_clause,[],[f193])).
% 1.58/0.57  fof(f193,plain,(
% 1.58/0.57    spl8_4 <=> sP2(sK5,sK6(k5_relat_1(sK4,sK5)),sK4)),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.58/0.57  fof(f440,plain,(
% 1.58/0.57    sK6(k5_relat_1(sK4,sK5)) = sK7(k5_relat_1(sK4,sK5)) | ~r2_hidden(sK6(k5_relat_1(sK4,sK5)),k1_relat_1(sK4)) | (~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(equality_resolution,[],[f419])).
% 1.58/0.57  fof(f419,plain,(
% 1.58/0.57    ( ! [X0] : (k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))) != k1_funct_1(sK4,X0) | sK7(k5_relat_1(sK4,sK5)) = X0 | ~r2_hidden(X0,k1_relat_1(sK4))) ) | (~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(subsumption_resolution,[],[f418,f70])).
% 1.58/0.57  fof(f70,plain,(
% 1.58/0.57    sP0(sK4)),
% 1.58/0.57    inference(subsumption_resolution,[],[f69,f43])).
% 1.58/0.57  fof(f43,plain,(
% 1.58/0.57    v2_funct_1(sK4)),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f69,plain,(
% 1.58/0.57    ~v2_funct_1(sK4) | sP0(sK4)),
% 1.58/0.57    inference(resolution,[],[f66,f46])).
% 1.58/0.57  fof(f46,plain,(
% 1.58/0.57    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f29])).
% 1.58/0.57  fof(f66,plain,(
% 1.58/0.57    sP1(sK4)),
% 1.58/0.57    inference(subsumption_resolution,[],[f64,f39])).
% 1.58/0.57  fof(f64,plain,(
% 1.58/0.57    sP1(sK4) | ~v1_relat_1(sK4)),
% 1.58/0.57    inference(resolution,[],[f53,f40])).
% 1.58/0.57  fof(f418,plain,(
% 1.58/0.57    ( ! [X0] : (k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))) != k1_funct_1(sK4,X0) | sK7(k5_relat_1(sK4,sK5)) = X0 | ~r2_hidden(X0,k1_relat_1(sK4)) | ~sP0(sK4)) ) | (~spl8_5 | ~spl8_11 | ~spl8_16)),
% 1.58/0.57    inference(subsumption_resolution,[],[f411,f302])).
% 1.58/0.57  fof(f302,plain,(
% 1.58/0.57    r2_hidden(sK7(k5_relat_1(sK4,sK5)),k1_relat_1(sK4)) | ~spl8_11),
% 1.58/0.57    inference(resolution,[],[f292,f59])).
% 1.58/0.57  fof(f292,plain,(
% 1.58/0.57    sP2(sK5,sK7(k5_relat_1(sK4,sK5)),sK4) | ~spl8_11),
% 1.58/0.57    inference(avatar_component_clause,[],[f290])).
% 1.58/0.57  fof(f290,plain,(
% 1.58/0.57    spl8_11 <=> sP2(sK5,sK7(k5_relat_1(sK4,sK5)),sK4)),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.58/0.57  fof(f411,plain,(
% 1.58/0.57    ( ! [X0] : (k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))) != k1_funct_1(sK4,X0) | sK7(k5_relat_1(sK4,sK5)) = X0 | ~r2_hidden(X0,k1_relat_1(sK4)) | ~r2_hidden(sK7(k5_relat_1(sK4,sK5)),k1_relat_1(sK4)) | ~sP0(sK4)) ) | (~spl8_5 | ~spl8_16)),
% 1.58/0.57    inference(superposition,[],[f48,f390])).
% 1.58/0.57  fof(f390,plain,(
% 1.58/0.57    k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))) | (~spl8_5 | ~spl8_16)),
% 1.58/0.57    inference(subsumption_resolution,[],[f389,f236])).
% 1.58/0.57  fof(f236,plain,(
% 1.58/0.57    r2_hidden(k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))),k1_relat_1(sK5)) | ~spl8_5),
% 1.58/0.57    inference(avatar_component_clause,[],[f235])).
% 1.58/0.57  fof(f235,plain,(
% 1.58/0.57    spl8_5 <=> r2_hidden(k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))),k1_relat_1(sK5))),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.58/0.57  fof(f389,plain,(
% 1.58/0.57    ~r2_hidden(k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))),k1_relat_1(sK5)) | k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))) | ~spl8_16),
% 1.58/0.57    inference(equality_resolution,[],[f386])).
% 1.58/0.57  fof(f386,plain,(
% 1.58/0.57    ( ! [X0] : (k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) != k1_funct_1(sK5,X0) | ~r2_hidden(X0,k1_relat_1(sK5)) | k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))) = X0) ) | ~spl8_16),
% 1.58/0.57    inference(avatar_component_clause,[],[f385])).
% 1.58/0.57  fof(f385,plain,(
% 1.58/0.57    spl8_16 <=> ! [X0] : (k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) != k1_funct_1(sK5,X0) | ~r2_hidden(X0,k1_relat_1(sK5)) | k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))) = X0)),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.58/0.57  fof(f48,plain,(
% 1.58/0.57    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~sP0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f33])).
% 1.58/0.57  fof(f33,plain,(
% 1.58/0.57    ! [X0] : ((sP0(X0) | (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f31,f32])).
% 1.58/0.57  fof(f32,plain,(
% 1.58/0.57    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0))))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f31,plain,(
% 1.58/0.57    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 1.58/0.57    inference(rectify,[],[f30])).
% 1.58/0.57  fof(f30,plain,(
% 1.58/0.57    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 1.58/0.57    inference(nnf_transformation,[],[f20])).
% 1.58/0.57  fof(f52,plain,(
% 1.58/0.57    ( ! [X0] : (sK6(X0) != sK7(X0) | sP0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f33])).
% 1.58/0.57  fof(f387,plain,(
% 1.58/0.57    ~spl8_12 | spl8_16 | ~spl8_1 | ~spl8_8),
% 1.58/0.57    inference(avatar_split_clause,[],[f315,f251,f145,f385,f327])).
% 1.58/0.57  fof(f327,plain,(
% 1.58/0.57    spl8_12 <=> r2_hidden(k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))),k1_relat_1(sK5))),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.58/0.57  fof(f145,plain,(
% 1.58/0.57    spl8_1 <=> r2_hidden(sK6(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5)))),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.58/0.57  fof(f251,plain,(
% 1.58/0.57    spl8_8 <=> r2_hidden(sK7(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5)))),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.58/0.57  fof(f315,plain,(
% 1.58/0.57    ( ! [X0] : (k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) != k1_funct_1(sK5,X0) | k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))) = X0 | ~r2_hidden(X0,k1_relat_1(sK5)) | ~r2_hidden(k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))),k1_relat_1(sK5))) ) | (~spl8_1 | ~spl8_8)),
% 1.58/0.57    inference(subsumption_resolution,[],[f308,f73])).
% 1.58/0.57  fof(f73,plain,(
% 1.58/0.57    sP0(sK5)),
% 1.58/0.57    inference(subsumption_resolution,[],[f72,f44])).
% 1.58/0.57  fof(f44,plain,(
% 1.58/0.57    v2_funct_1(sK5)),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f72,plain,(
% 1.58/0.57    ~v2_funct_1(sK5) | sP0(sK5)),
% 1.58/0.57    inference(resolution,[],[f67,f46])).
% 1.58/0.57  fof(f67,plain,(
% 1.58/0.57    sP1(sK5)),
% 1.58/0.57    inference(subsumption_resolution,[],[f65,f41])).
% 1.58/0.57  fof(f65,plain,(
% 1.58/0.57    sP1(sK5) | ~v1_relat_1(sK5)),
% 1.58/0.57    inference(resolution,[],[f53,f42])).
% 1.58/0.57  fof(f308,plain,(
% 1.58/0.57    ( ! [X0] : (k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) != k1_funct_1(sK5,X0) | k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))) = X0 | ~r2_hidden(X0,k1_relat_1(sK5)) | ~r2_hidden(k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))),k1_relat_1(sK5)) | ~sP0(sK5)) ) | (~spl8_1 | ~spl8_8)),
% 1.58/0.57    inference(superposition,[],[f48,f273])).
% 1.58/0.57  fof(f273,plain,(
% 1.58/0.57    k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5)))) | (~spl8_1 | ~spl8_8)),
% 1.58/0.57    inference(forward_demodulation,[],[f272,f178])).
% 1.58/0.57  fof(f178,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) | ~spl8_1),
% 1.58/0.57    inference(backward_demodulation,[],[f133,f177])).
% 1.58/0.57  fof(f177,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) | ~spl8_1),
% 1.58/0.57    inference(subsumption_resolution,[],[f176,f41])).
% 1.58/0.57  fof(f176,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) | ~v1_relat_1(sK5) | ~spl8_1),
% 1.58/0.57    inference(subsumption_resolution,[],[f175,f42])).
% 1.58/0.57  fof(f175,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~spl8_1),
% 1.58/0.57    inference(subsumption_resolution,[],[f174,f39])).
% 1.58/0.57  fof(f174,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) | ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~spl8_1),
% 1.58/0.57    inference(subsumption_resolution,[],[f172,f40])).
% 1.58/0.57  fof(f172,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5)))) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~spl8_1),
% 1.58/0.57    inference(resolution,[],[f146,f56])).
% 1.58/0.57  fof(f56,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f15])).
% 1.58/0.57  fof(f15,plain,(
% 1.58/0.57    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(flattening,[],[f14])).
% 1.58/0.57  fof(f14,plain,(
% 1.58/0.57    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f5])).
% 1.58/0.57  fof(f5,axiom,(
% 1.58/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 1.58/0.57  fof(f146,plain,(
% 1.58/0.57    r2_hidden(sK6(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5))) | ~spl8_1),
% 1.58/0.57    inference(avatar_component_clause,[],[f145])).
% 1.58/0.57  fof(f133,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5)))),
% 1.58/0.57    inference(subsumption_resolution,[],[f132,f40])).
% 1.58/0.57  fof(f132,plain,(
% 1.58/0.57    ~v1_funct_1(sK4) | k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5)))),
% 1.58/0.57    inference(subsumption_resolution,[],[f131,f41])).
% 1.58/0.57  fof(f131,plain,(
% 1.58/0.57    ~v1_relat_1(sK5) | ~v1_funct_1(sK4) | k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5)))),
% 1.58/0.57    inference(subsumption_resolution,[],[f130,f42])).
% 1.58/0.57  fof(f130,plain,(
% 1.58/0.57    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~v1_funct_1(sK4) | k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5)))),
% 1.58/0.57    inference(subsumption_resolution,[],[f127,f39])).
% 1.58/0.57  fof(f127,plain,(
% 1.58/0.57    ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~v1_funct_1(sK4) | k1_funct_1(k5_relat_1(sK4,sK5),sK6(k5_relat_1(sK4,sK5))) = k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5)))),
% 1.58/0.57    inference(resolution,[],[f85,f45])).
% 1.58/0.57  fof(f85,plain,(
% 1.58/0.57    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | k1_funct_1(k5_relat_1(X0,X1),sK6(k5_relat_1(X0,X1))) = k1_funct_1(k5_relat_1(X0,X1),sK7(k5_relat_1(X0,X1)))) )),
% 1.58/0.57    inference(resolution,[],[f76,f51])).
% 1.58/0.57  fof(f51,plain,(
% 1.58/0.57    ( ! [X0] : (sP0(X0) | k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f33])).
% 1.58/0.57  fof(f272,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5)))) | ~spl8_8),
% 1.58/0.57    inference(subsumption_resolution,[],[f271,f41])).
% 1.58/0.57  fof(f271,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5)))) | ~v1_relat_1(sK5) | ~spl8_8),
% 1.58/0.57    inference(subsumption_resolution,[],[f270,f42])).
% 1.58/0.57  fof(f270,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5)))) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~spl8_8),
% 1.58/0.57    inference(subsumption_resolution,[],[f269,f39])).
% 1.58/0.57  fof(f269,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5)))) | ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~spl8_8),
% 1.58/0.57    inference(subsumption_resolution,[],[f267,f40])).
% 1.58/0.57  fof(f267,plain,(
% 1.58/0.57    k1_funct_1(k5_relat_1(sK4,sK5),sK7(k5_relat_1(sK4,sK5))) = k1_funct_1(sK5,k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5)))) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~spl8_8),
% 1.58/0.57    inference(resolution,[],[f252,f56])).
% 1.58/0.57  fof(f252,plain,(
% 1.58/0.57    r2_hidden(sK7(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5))) | ~spl8_8),
% 1.58/0.57    inference(avatar_component_clause,[],[f251])).
% 1.58/0.57  fof(f336,plain,(
% 1.58/0.57    ~spl8_11 | spl8_12),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f335])).
% 1.58/0.57  fof(f335,plain,(
% 1.58/0.57    $false | (~spl8_11 | spl8_12)),
% 1.58/0.57    inference(subsumption_resolution,[],[f334,f292])).
% 1.58/0.57  fof(f334,plain,(
% 1.58/0.57    ~sP2(sK5,sK7(k5_relat_1(sK4,sK5)),sK4) | spl8_12),
% 1.58/0.57    inference(resolution,[],[f329,f60])).
% 1.58/0.57  fof(f60,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0)) | ~sP2(X0,X1,X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f38])).
% 1.58/0.57  fof(f329,plain,(
% 1.58/0.57    ~r2_hidden(k1_funct_1(sK4,sK7(k5_relat_1(sK4,sK5))),k1_relat_1(sK5)) | spl8_12),
% 1.58/0.57    inference(avatar_component_clause,[],[f327])).
% 1.58/0.57  fof(f299,plain,(
% 1.58/0.57    spl8_10),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f298])).
% 1.58/0.57  fof(f298,plain,(
% 1.58/0.57    $false | spl8_10),
% 1.58/0.57    inference(subsumption_resolution,[],[f297,f41])).
% 1.58/0.57  fof(f297,plain,(
% 1.58/0.57    ~v1_relat_1(sK5) | spl8_10),
% 1.58/0.57    inference(subsumption_resolution,[],[f296,f42])).
% 1.58/0.57  fof(f296,plain,(
% 1.58/0.57    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl8_10),
% 1.58/0.57    inference(subsumption_resolution,[],[f295,f39])).
% 1.58/0.57  fof(f295,plain,(
% 1.58/0.57    ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl8_10),
% 1.58/0.57    inference(subsumption_resolution,[],[f294,f40])).
% 1.58/0.57  fof(f294,plain,(
% 1.58/0.57    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl8_10),
% 1.58/0.57    inference(resolution,[],[f288,f62])).
% 1.58/0.57  fof(f62,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (sP3(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f25])).
% 1.58/0.57  fof(f25,plain,(
% 1.58/0.57    ! [X0,X1] : (! [X2] : (sP3(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(definition_folding,[],[f17,f24,f23])).
% 1.58/0.57  fof(f24,plain,(
% 1.58/0.57    ! [X2,X0,X1] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> sP2(X1,X0,X2)) | ~sP3(X2,X0,X1))),
% 1.58/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.58/0.57  fof(f17,plain,(
% 1.58/0.57    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(flattening,[],[f16])).
% 1.58/0.57  fof(f16,plain,(
% 1.58/0.57    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f4])).
% 1.58/0.57  fof(f4,axiom,(
% 1.58/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 1.58/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 1.58/0.57  fof(f288,plain,(
% 1.58/0.57    ~sP3(sK4,sK7(k5_relat_1(sK4,sK5)),sK5) | spl8_10),
% 1.58/0.57    inference(avatar_component_clause,[],[f286])).
% 1.58/0.57  fof(f286,plain,(
% 1.58/0.57    spl8_10 <=> sP3(sK4,sK7(k5_relat_1(sK4,sK5)),sK5)),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.58/0.57  fof(f293,plain,(
% 1.58/0.57    ~spl8_10 | spl8_11 | ~spl8_8),
% 1.58/0.57    inference(avatar_split_clause,[],[f268,f251,f290,f286])).
% 1.58/0.57  fof(f268,plain,(
% 1.58/0.57    sP2(sK5,sK7(k5_relat_1(sK4,sK5)),sK4) | ~sP3(sK4,sK7(k5_relat_1(sK4,sK5)),sK5) | ~spl8_8),
% 1.58/0.57    inference(resolution,[],[f252,f57])).
% 1.58/0.57  fof(f57,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2))) | sP2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f35])).
% 1.58/0.57  fof(f35,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (((r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2))) | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2))))) | ~sP3(X0,X1,X2))),
% 1.58/0.57    inference(rectify,[],[f34])).
% 1.58/0.57  fof(f34,plain,(
% 1.58/0.57    ! [X2,X0,X1] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~sP3(X2,X0,X1))),
% 1.58/0.57    inference(nnf_transformation,[],[f24])).
% 1.58/0.57  fof(f266,plain,(
% 1.58/0.57    spl8_8),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f265])).
% 1.58/0.57  fof(f265,plain,(
% 1.58/0.57    $false | spl8_8),
% 1.58/0.57    inference(subsumption_resolution,[],[f264,f45])).
% 1.58/0.57  fof(f264,plain,(
% 1.58/0.57    v2_funct_1(k5_relat_1(sK4,sK5)) | spl8_8),
% 1.58/0.57    inference(subsumption_resolution,[],[f263,f41])).
% 1.58/0.57  fof(f263,plain,(
% 1.58/0.57    ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | spl8_8),
% 1.58/0.57    inference(subsumption_resolution,[],[f262,f42])).
% 1.58/0.57  fof(f262,plain,(
% 1.58/0.57    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | spl8_8),
% 1.58/0.57    inference(subsumption_resolution,[],[f261,f39])).
% 1.58/0.57  fof(f261,plain,(
% 1.58/0.57    ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | spl8_8),
% 1.58/0.57    inference(subsumption_resolution,[],[f260,f40])).
% 1.58/0.57  fof(f260,plain,(
% 1.58/0.57    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | spl8_8),
% 1.58/0.57    inference(resolution,[],[f259,f76])).
% 1.58/0.57  fof(f259,plain,(
% 1.58/0.57    sP0(k5_relat_1(sK4,sK5)) | spl8_8),
% 1.58/0.57    inference(resolution,[],[f253,f50])).
% 1.58/0.57  fof(f50,plain,(
% 1.58/0.57    ( ! [X0] : (r2_hidden(sK7(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f33])).
% 1.58/0.57  fof(f253,plain,(
% 1.58/0.57    ~r2_hidden(sK7(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5))) | spl8_8),
% 1.58/0.57    inference(avatar_component_clause,[],[f251])).
% 1.58/0.57  fof(f244,plain,(
% 1.58/0.57    ~spl8_4 | spl8_5),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f243])).
% 1.58/0.57  fof(f243,plain,(
% 1.58/0.57    $false | (~spl8_4 | spl8_5)),
% 1.58/0.57    inference(subsumption_resolution,[],[f242,f195])).
% 1.58/0.57  fof(f242,plain,(
% 1.58/0.57    ~sP2(sK5,sK6(k5_relat_1(sK4,sK5)),sK4) | spl8_5),
% 1.58/0.57    inference(resolution,[],[f237,f60])).
% 1.58/0.57  fof(f237,plain,(
% 1.58/0.57    ~r2_hidden(k1_funct_1(sK4,sK6(k5_relat_1(sK4,sK5))),k1_relat_1(sK5)) | spl8_5),
% 1.58/0.57    inference(avatar_component_clause,[],[f235])).
% 1.58/0.57  fof(f202,plain,(
% 1.58/0.57    spl8_3),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f201])).
% 1.58/0.57  fof(f201,plain,(
% 1.58/0.57    $false | spl8_3),
% 1.58/0.57    inference(subsumption_resolution,[],[f200,f41])).
% 1.58/0.57  fof(f200,plain,(
% 1.58/0.57    ~v1_relat_1(sK5) | spl8_3),
% 1.58/0.57    inference(subsumption_resolution,[],[f199,f42])).
% 1.58/0.57  fof(f199,plain,(
% 1.58/0.57    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl8_3),
% 1.58/0.57    inference(subsumption_resolution,[],[f198,f39])).
% 1.58/0.57  fof(f198,plain,(
% 1.58/0.57    ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl8_3),
% 1.58/0.57    inference(subsumption_resolution,[],[f197,f40])).
% 1.58/0.57  fof(f197,plain,(
% 1.58/0.57    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl8_3),
% 1.58/0.57    inference(resolution,[],[f191,f62])).
% 1.58/0.57  fof(f191,plain,(
% 1.58/0.57    ~sP3(sK4,sK6(k5_relat_1(sK4,sK5)),sK5) | spl8_3),
% 1.58/0.57    inference(avatar_component_clause,[],[f189])).
% 1.58/0.57  fof(f189,plain,(
% 1.58/0.57    spl8_3 <=> sP3(sK4,sK6(k5_relat_1(sK4,sK5)),sK5)),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.58/0.57  fof(f196,plain,(
% 1.58/0.57    ~spl8_3 | spl8_4 | ~spl8_1),
% 1.58/0.57    inference(avatar_split_clause,[],[f173,f145,f193,f189])).
% 1.58/0.57  fof(f173,plain,(
% 1.58/0.57    sP2(sK5,sK6(k5_relat_1(sK4,sK5)),sK4) | ~sP3(sK4,sK6(k5_relat_1(sK4,sK5)),sK5) | ~spl8_1),
% 1.58/0.57    inference(resolution,[],[f146,f57])).
% 1.58/0.57  fof(f171,plain,(
% 1.58/0.57    spl8_1),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f170])).
% 1.58/0.57  fof(f170,plain,(
% 1.58/0.57    $false | spl8_1),
% 1.58/0.57    inference(subsumption_resolution,[],[f169,f45])).
% 1.58/0.57  fof(f169,plain,(
% 1.58/0.57    v2_funct_1(k5_relat_1(sK4,sK5)) | spl8_1),
% 1.58/0.57    inference(subsumption_resolution,[],[f168,f41])).
% 1.58/0.57  fof(f168,plain,(
% 1.58/0.57    ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | spl8_1),
% 1.58/0.57    inference(subsumption_resolution,[],[f167,f42])).
% 1.58/0.57  fof(f167,plain,(
% 1.58/0.57    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | spl8_1),
% 1.58/0.57    inference(subsumption_resolution,[],[f166,f39])).
% 1.58/0.57  fof(f166,plain,(
% 1.58/0.57    ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | spl8_1),
% 1.58/0.57    inference(subsumption_resolution,[],[f165,f40])).
% 1.58/0.57  fof(f165,plain,(
% 1.58/0.57    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | v2_funct_1(k5_relat_1(sK4,sK5)) | spl8_1),
% 1.58/0.57    inference(resolution,[],[f153,f76])).
% 1.58/0.57  fof(f153,plain,(
% 1.58/0.57    sP0(k5_relat_1(sK4,sK5)) | spl8_1),
% 1.58/0.57    inference(resolution,[],[f147,f49])).
% 1.58/0.57  fof(f49,plain,(
% 1.58/0.57    ( ! [X0] : (r2_hidden(sK6(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f33])).
% 1.58/0.57  fof(f147,plain,(
% 1.58/0.57    ~r2_hidden(sK6(k5_relat_1(sK4,sK5)),k1_relat_1(k5_relat_1(sK4,sK5))) | spl8_1),
% 1.58/0.57    inference(avatar_component_clause,[],[f145])).
% 1.58/0.57  % SZS output end Proof for theBenchmark
% 1.58/0.57  % (21609)------------------------------
% 1.58/0.57  % (21609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (21609)Termination reason: Refutation
% 1.58/0.57  
% 1.58/0.57  % (21609)Memory used [KB]: 11001
% 1.58/0.57  % (21609)Time elapsed: 0.160 s
% 1.58/0.57  % (21609)------------------------------
% 1.58/0.57  % (21609)------------------------------
% 1.58/0.58  % (21583)Success in time 0.21 s
%------------------------------------------------------------------------------
