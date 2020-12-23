%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  195 (17468 expanded)
%              Number of leaves         :   27 (5194 expanded)
%              Depth                    :   59
%              Number of atoms          :  763 (78754 expanded)
%              Number of equality atoms :  155 (17267 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f441,plain,(
    $false ),
    inference(subsumption_resolution,[],[f440,f147])).

fof(f147,plain,(
    r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK6)) ),
    inference(resolution,[],[f146,f76])).

fof(f76,plain,(
    r4_wellord1(k1_wellord2(sK6),k1_wellord2(sK7)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( sK6 != sK7
    & r4_wellord1(k1_wellord2(sK6),k1_wellord2(sK7))
    & v3_ordinal1(sK7)
    & v3_ordinal1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f17,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK6 != X1
          & r4_wellord1(k1_wellord2(sK6),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( sK6 != X1
        & r4_wellord1(k1_wellord2(sK6),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK6 != sK7
      & r4_wellord1(k1_wellord2(sK6),k1_wellord2(sK7))
      & v3_ordinal1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0)) ) ),
    inference(resolution,[],[f141,f78])).

fof(f78,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r4_wellord1(k1_wellord2(X0),X1)
      | r4_wellord1(X1,k1_wellord2(X0)) ) ),
    inference(resolution,[],[f80,f78])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | r4_wellord1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f440,plain,(
    ~ r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK6)) ),
    inference(backward_demodulation,[],[f416,f435])).

fof(f435,plain,(
    k1_wellord2(sK6) = k2_wellord1(k1_wellord2(sK7),sK6) ),
    inference(resolution,[],[f433,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f433,plain,(
    r1_tarski(sK6,sK7) ),
    inference(resolution,[],[f425,f323])).

fof(f323,plain,(
    sP0(k1_wellord2(sK7),sK6,sK6) ),
    inference(subsumption_resolution,[],[f322,f78])).

fof(f322,plain,
    ( sP0(k1_wellord2(sK7),sK6,sK6)
    | ~ v1_relat_1(k1_wellord2(sK7)) ),
    inference(resolution,[],[f319,f89])).

fof(f89,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f22,f35,f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(k4_tarski(X3,X1),X0)
            & X1 != X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> sP0(X0,X1,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f319,plain,
    ( ~ sP1(k1_wellord2(sK7))
    | sP0(k1_wellord2(sK7),sK6,sK6) ),
    inference(superposition,[],[f119,f309])).

fof(f309,plain,(
    sK6 = k1_wellord1(k1_wellord2(sK7),sK6) ),
    inference(subsumption_resolution,[],[f308,f75])).

fof(f75,plain,(
    v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f308,plain,
    ( sK6 = k1_wellord1(k1_wellord2(sK7),sK6)
    | ~ v3_ordinal1(sK7) ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,
    ( sK6 = k1_wellord1(k1_wellord2(sK7),sK6)
    | ~ v3_ordinal1(sK7)
    | sK6 = k1_wellord1(k1_wellord2(sK7),sK6) ),
    inference(resolution,[],[f301,f168])).

fof(f168,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6,X0)
      | ~ v3_ordinal1(X0)
      | sK6 = k1_wellord1(k1_wellord2(X0),sK6) ) ),
    inference(resolution,[],[f91,f74])).

fof(f74,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f301,plain,
    ( r2_hidden(sK6,sK7)
    | sK6 = k1_wellord1(k1_wellord2(sK7),sK6) ),
    inference(resolution,[],[f300,f175])).

fof(f175,plain,
    ( r2_hidden(sK7,sK6)
    | r2_hidden(sK6,sK7) ),
    inference(subsumption_resolution,[],[f173,f77])).

fof(f77,plain,(
    sK6 != sK7 ),
    inference(cnf_transformation,[],[f45])).

fof(f173,plain,
    ( r2_hidden(sK6,sK7)
    | sK6 = sK7
    | r2_hidden(sK7,sK6) ),
    inference(resolution,[],[f170,f75])).

fof(f170,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(sK6,X0)
      | sK6 = X0
      | r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f92,f74])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f300,plain,
    ( ~ r2_hidden(sK7,sK6)
    | sK6 = k1_wellord1(k1_wellord2(sK7),sK6) ),
    inference(subsumption_resolution,[],[f299,f76])).

fof(f299,plain,
    ( ~ r4_wellord1(k1_wellord2(sK6),k1_wellord2(sK7))
    | ~ r2_hidden(sK7,sK6)
    | sK6 = k1_wellord1(k1_wellord2(sK7),sK6) ),
    inference(superposition,[],[f258,f281])).

fof(f281,plain,
    ( k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7)
    | sK6 = k1_wellord1(k1_wellord2(sK7),sK6) ),
    inference(resolution,[],[f279,f112])).

fof(f279,plain,
    ( r1_tarski(sK7,sK6)
    | sK6 = k1_wellord1(k1_wellord2(sK7),sK6) ),
    inference(subsumption_resolution,[],[f275,f75])).

fof(f275,plain,
    ( r1_tarski(sK7,sK6)
    | ~ v3_ordinal1(sK7)
    | sK6 = k1_wellord1(k1_wellord2(sK7),sK6) ),
    inference(resolution,[],[f274,f168])).

fof(f274,plain,
    ( r2_hidden(sK6,sK7)
    | r1_tarski(sK7,sK6) ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,
    ( r2_hidden(sK6,sK7)
    | r1_tarski(sK7,sK6)
    | r1_tarski(sK7,sK6) ),
    inference(resolution,[],[f266,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK14(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK14(X0,X1),X1)
          & r2_hidden(sK14(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f71,f72])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK14(X0,X1),X1)
        & r2_hidden(sK14(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f266,plain,(
    ! [X1] :
      ( r2_hidden(sK14(sK7,X1),sK6)
      | r2_hidden(sK6,sK7)
      | r1_tarski(sK7,X1) ) ),
    inference(resolution,[],[f264,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK14(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f264,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK7)
      | r2_hidden(X0,sK6)
      | r2_hidden(sK6,sK7) ) ),
    inference(resolution,[],[f254,f175])).

fof(f254,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7,sK6)
      | ~ r2_hidden(X0,sK7)
      | r2_hidden(X0,sK6) ) ),
    inference(superposition,[],[f196,f253])).

fof(f253,plain,(
    sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(subsumption_resolution,[],[f252,f147])).

fof(f252,plain,
    ( ~ r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK6))
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(duplicate_literal_removal,[],[f251])).

fof(f251,plain,
    ( ~ r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK6))
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(superposition,[],[f218,f235])).

fof(f235,plain,
    ( k1_wellord2(sK6) = k2_wellord1(k1_wellord2(sK7),sK6)
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(resolution,[],[f233,f112])).

fof(f233,plain,
    ( r1_tarski(sK6,sK7)
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,
    ( sK7 = k1_wellord1(k1_wellord2(sK6),sK7)
    | r1_tarski(sK6,sK7)
    | r1_tarski(sK6,sK7) ),
    inference(resolution,[],[f226,f118])).

fof(f226,plain,(
    ! [X1] :
      ( r2_hidden(sK14(sK6,X1),sK7)
      | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)
      | r1_tarski(sK6,X1) ) ),
    inference(resolution,[],[f223,f117])).

fof(f223,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK6)
      | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)
      | r2_hidden(X0,sK7) ) ),
    inference(subsumption_resolution,[],[f222,f178])).

fof(f178,plain,
    ( r2_hidden(sK6,sK7)
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(subsumption_resolution,[],[f176,f74])).

fof(f176,plain,
    ( r2_hidden(sK6,sK7)
    | ~ v3_ordinal1(sK6)
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(resolution,[],[f175,f169])).

fof(f169,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK7,X1)
      | ~ v3_ordinal1(X1)
      | sK7 = k1_wellord1(k1_wellord2(X1),sK7) ) ),
    inference(resolution,[],[f91,f75])).

fof(f222,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK6)
      | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)
      | ~ r2_hidden(sK6,sK7)
      | r2_hidden(X0,sK7) ) ),
    inference(subsumption_resolution,[],[f219,f75])).

fof(f219,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK6)
      | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)
      | ~ r2_hidden(sK6,sK7)
      | r2_hidden(X0,sK7)
      | ~ v3_ordinal1(sK7) ) ),
    inference(resolution,[],[f193,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f97,f154])).

fof(f154,plain,(
    ! [X0] :
      ( sP2(X0,k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f153,f138])).

fof(f138,plain,(
    ! [X0] :
      ( ~ sP3(k1_wellord2(X0),X0)
      | sP2(X0,k1_wellord2(X0)) ) ),
    inference(superposition,[],[f122,f137])).

fof(f137,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f136,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | k3_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ( ( ~ r1_tarski(sK12(X0,X1),sK13(X0,X1))
            | ~ r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0) )
          & ( r1_tarski(sK12(X0,X1),sK13(X0,X1))
            | r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0) )
          & r2_hidden(sK13(X0,X1),X1)
          & r2_hidden(sK12(X0,X1),X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP4(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f65,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X0) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ( ~ r1_tarski(sK12(X0,X1),sK13(X0,X1))
          | ~ r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0) )
        & ( r1_tarski(sK12(X0,X1),sK13(X0,X1))
          | r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0) )
        & r2_hidden(sK13(X0,X1),X1)
        & r2_hidden(sK12(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X0) )
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP4(X0,X1) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ( sP4(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP4(X1,X0) ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ( sP4(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP4(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( sP4(X1,X0)
    <=> ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
            <=> r1_tarski(X2,X3) )
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f136,plain,(
    ! [X0] : sP4(k1_wellord2(X0),X0) ),
    inference(subsumption_resolution,[],[f135,f78])).

fof(f135,plain,(
    ! [X0] :
      ( sP4(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f123,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( sP5(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP5(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f31,f41,f40])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> sP4(X1,X0) )
      | ~ sP5(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f123,plain,(
    ! [X0] :
      ( ~ sP5(X0,k1_wellord2(X0))
      | sP4(k1_wellord2(X0),X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | k1_wellord2(X0) != X1
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP4(X1,X0) )
        & ( sP4(X1,X0)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP5(X0,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f122,plain,(
    ! [X0] :
      ( ~ sP3(X0,k3_relat_1(X0))
      | sP2(k3_relat_1(X0),X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k3_relat_1(X0) != X1
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_wellord1(X0,sK9(X0,X1)) = X1
            & r2_hidden(sK9(X0,X1),k3_relat_1(X0)) )
          | k3_relat_1(X0) = X1
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ( ! [X3] :
                ( k1_wellord1(X0,X3) != X1
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
            & k3_relat_1(X0) != X1 ) ) )
      | ~ sP3(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_wellord1(X0,X2) = X1
          & r2_hidden(X2,k3_relat_1(X0)) )
     => ( k1_wellord1(X0,sK9(X0,X1)) = X1
        & r2_hidden(sK9(X0,X1),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X0,X2) = X1
              & r2_hidden(X2,k3_relat_1(X0)) )
          | k3_relat_1(X0) = X1
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ( ! [X3] :
                ( k1_wellord1(X0,X3) != X1
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
            & k3_relat_1(X0) != X1 ) ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ sP3(X1,X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f153,plain,(
    ! [X0] :
      ( sP3(k1_wellord2(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f152,f128])).

fof(f128,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
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

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | sP3(k1_wellord2(X1),X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f151,f137])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_relat_1(k1_wellord2(X1)))
      | sP3(k1_wellord2(X1),X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f150,f78])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_relat_1(k1_wellord2(X1)))
      | sP3(k1_wellord2(X1),X0)
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f101,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f29,f38,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X3] :
          ( ! [X4] :
              ( r2_hidden(X4,X0)
              | ~ r2_hidden(k4_tarski(X4,X3),X1) )
          | ~ r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X3] :
              ( r2_hidden(X3,X0)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X1)
                 => r2_hidden(X4,X0) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X2] :
              ( r2_hidden(X2,X0)
             => ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X2),X1)
                 => r2_hidden(X3,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).

fof(f97,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP2(X0,X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X5,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X0)
          & r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r2_hidden(k4_tarski(X5,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f58,f60,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r2_hidden(k4_tarski(X3,X2),X1) )
          & r2_hidden(X2,X0) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r2_hidden(k4_tarski(X3,sK10(X0,X1)),X1) )
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(k4_tarski(X3,sK10(X0,X1)),X1) )
     => ( ~ r2_hidden(sK11(X0,X1),X0)
        & r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r2_hidden(k4_tarski(X3,X2),X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r2_hidden(k4_tarski(X5,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(X4,X0)
                & r2_hidden(k4_tarski(X4,X3),X1) )
            & r2_hidden(X3,X0) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f193,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK6),k1_wellord2(sK7))
      | ~ r2_hidden(X0,sK6)
      | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ) ),
    inference(resolution,[],[f191,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
            | sK8(X0,X1,X2) = X1
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
              & sK8(X0,X1,X2) != X1 )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k4_tarski(X4,X1),X0)
              | X1 = X4 )
            & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                & X1 != X4 )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
          | sK8(X0,X1,X2) = X1
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
            & sK8(X0,X1,X2) != X1 )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k4_tarski(X4,X1),X0)
              | X1 = X4 )
            & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                & X1 != X4 )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3 )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3 )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f191,plain,
    ( sP0(k1_wellord2(sK7),sK6,sK6)
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(subsumption_resolution,[],[f190,f78])).

fof(f190,plain,
    ( sP0(k1_wellord2(sK7),sK6,sK6)
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)
    | ~ v1_relat_1(k1_wellord2(sK7)) ),
    inference(resolution,[],[f185,f89])).

fof(f185,plain,
    ( ~ sP1(k1_wellord2(sK7))
    | sP0(k1_wellord2(sK7),sK6,sK6)
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(superposition,[],[f119,f181])).

fof(f181,plain,
    ( sK6 = k1_wellord1(k1_wellord2(sK7),sK6)
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(subsumption_resolution,[],[f179,f75])).

fof(f179,plain,
    ( sK7 = k1_wellord1(k1_wellord2(sK6),sK7)
    | ~ v3_ordinal1(sK7)
    | sK6 = k1_wellord1(k1_wellord2(sK7),sK6) ),
    inference(resolution,[],[f178,f168])).

fof(f218,plain,
    ( ~ r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6))
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(subsumption_resolution,[],[f217,f178])).

fof(f217,plain,
    ( ~ r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6))
    | ~ r2_hidden(sK6,sK7)
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(subsumption_resolution,[],[f216,f75])).

fof(f216,plain,
    ( ~ r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6))
    | ~ r2_hidden(sK6,sK7)
    | ~ v3_ordinal1(sK7)
    | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) ),
    inference(superposition,[],[f213,f181])).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f212,f137])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f211,f78])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f79,f90])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(k1_wellord2(sK6),X1))
      | ~ r2_hidden(X1,sK6)
      | r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f194,f74])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,k1_wellord1(k1_wellord2(X1),X0)) ) ),
    inference(resolution,[],[f186,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
      | ~ r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X2)) ) ),
    inference(resolution,[],[f165,f78])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(resolution,[],[f161,f89])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1)
      | r2_hidden(k4_tarski(X0,X2),X1)
      | ~ r2_hidden(X0,k1_wellord1(X1,X2)) ) ),
    inference(resolution,[],[f84,f119])).

fof(f258,plain,
    ( ~ r4_wellord1(k1_wellord2(sK6),k2_wellord1(k1_wellord2(sK6),sK7))
    | ~ r2_hidden(sK7,sK6) ),
    inference(subsumption_resolution,[],[f255,f74])).

fof(f255,plain,
    ( ~ r4_wellord1(k1_wellord2(sK6),k2_wellord1(k1_wellord2(sK6),sK7))
    | ~ r2_hidden(sK7,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(superposition,[],[f213,f253])).

fof(f119,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k1_wellord1(X0,X1))
      | ~ sP1(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ~ sP0(X0,X1,X2) )
          & ( sP0(X0,X1,X2)
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f425,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK6,sK6)
      | r1_tarski(sK6,sK7) ) ),
    inference(resolution,[],[f418,f120])).

fof(f120,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | ~ sP0(X0,X4,X2) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f418,plain,
    ( r2_hidden(sK6,sK6)
    | r1_tarski(sK6,sK7) ),
    inference(resolution,[],[f413,f347])).

fof(f347,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK7)
      | r1_tarski(sK6,sK7)
      | r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f344,f116])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f344,plain,
    ( r1_tarski(sK7,sK6)
    | r1_tarski(sK6,sK7) ),
    inference(duplicate_literal_removal,[],[f340])).

fof(f340,plain,
    ( r1_tarski(sK6,sK7)
    | r1_tarski(sK7,sK6)
    | r1_tarski(sK6,sK7) ),
    inference(resolution,[],[f315,f118])).

fof(f315,plain,(
    ! [X1] :
      ( r2_hidden(sK14(sK6,X1),sK7)
      | r1_tarski(sK6,X1)
      | r1_tarski(sK7,sK6) ) ),
    inference(forward_demodulation,[],[f312,f309])).

fof(f312,plain,(
    ! [X1] :
      ( r2_hidden(sK14(sK6,X1),sK7)
      | r1_tarski(sK7,sK6)
      | r1_tarski(k1_wellord1(k1_wellord2(sK7),sK6),X1) ) ),
    inference(backward_demodulation,[],[f293,f309])).

fof(f293,plain,(
    ! [X1] :
      ( r2_hidden(sK14(k1_wellord1(k1_wellord2(sK7),sK6),X1),sK7)
      | r1_tarski(sK7,sK6)
      | r1_tarski(k1_wellord1(k1_wellord2(sK7),sK6),X1) ) ),
    inference(resolution,[],[f277,f117])).

fof(f277,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_wellord1(k1_wellord2(sK7),sK6))
      | r2_hidden(X0,sK7)
      | r1_tarski(sK7,sK6) ) ),
    inference(resolution,[],[f274,f197])).

fof(f197,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK7)
      | r2_hidden(X2,sK7)
      | ~ r2_hidden(X2,k1_wellord1(k1_wellord2(sK7),X3)) ) ),
    inference(resolution,[],[f194,f75])).

fof(f413,plain,(
    r2_hidden(sK6,sK7) ),
    inference(subsumption_resolution,[],[f175,f412])).

fof(f412,plain,(
    ~ r2_hidden(sK7,sK6) ),
    inference(subsumption_resolution,[],[f411,f76])).

fof(f411,plain,
    ( ~ r4_wellord1(k1_wellord2(sK6),k1_wellord2(sK7))
    | ~ r2_hidden(sK7,sK6) ),
    inference(backward_demodulation,[],[f258,f410])).

fof(f410,plain,(
    k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7) ),
    inference(subsumption_resolution,[],[f409,f112])).

fof(f409,plain,
    ( k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7)
    | r1_tarski(sK7,sK6) ),
    inference(resolution,[],[f408,f274])).

fof(f408,plain,
    ( ~ r2_hidden(sK6,sK7)
    | k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7) ),
    inference(subsumption_resolution,[],[f407,f147])).

fof(f407,plain,
    ( ~ r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK6))
    | ~ r2_hidden(sK6,sK7)
    | k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7) ),
    inference(superposition,[],[f320,f363])).

fof(f363,plain,
    ( k1_wellord2(sK6) = k2_wellord1(k1_wellord2(sK7),sK6)
    | k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7) ),
    inference(resolution,[],[f346,f112])).

fof(f346,plain,
    ( r1_tarski(sK6,sK7)
    | k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7) ),
    inference(resolution,[],[f344,f112])).

fof(f320,plain,
    ( ~ r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6))
    | ~ r2_hidden(sK6,sK7) ),
    inference(subsumption_resolution,[],[f317,f75])).

fof(f317,plain,
    ( ~ r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6))
    | ~ r2_hidden(sK6,sK7)
    | ~ v3_ordinal1(sK7) ),
    inference(superposition,[],[f213,f309])).

fof(f416,plain,(
    ~ r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6)) ),
    inference(subsumption_resolution,[],[f320,f413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:11:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (30340)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.46  % (30349)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (30363)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (30344)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (30336)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (30336)Refutation not found, incomplete strategy% (30336)------------------------------
% 0.22/0.51  % (30336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30336)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30336)Memory used [KB]: 1663
% 0.22/0.51  % (30336)Time elapsed: 0.099 s
% 0.22/0.51  % (30336)------------------------------
% 0.22/0.51  % (30336)------------------------------
% 0.22/0.52  % (30355)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (30360)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (30346)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (30347)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (30356)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (30346)Refutation not found, incomplete strategy% (30346)------------------------------
% 0.22/0.52  % (30346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30346)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30346)Memory used [KB]: 10746
% 0.22/0.52  % (30346)Time elapsed: 0.103 s
% 0.22/0.52  % (30346)------------------------------
% 0.22/0.52  % (30346)------------------------------
% 0.22/0.52  % (30337)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (30339)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (30345)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (30343)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (30353)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (30363)Refutation not found, incomplete strategy% (30363)------------------------------
% 0.22/0.52  % (30363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30363)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30363)Memory used [KB]: 10746
% 0.22/0.52  % (30363)Time elapsed: 0.106 s
% 0.22/0.52  % (30363)------------------------------
% 0.22/0.52  % (30363)------------------------------
% 0.22/0.52  % (30348)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (30341)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (30361)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (30348)Refutation not found, incomplete strategy% (30348)------------------------------
% 0.22/0.53  % (30348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30348)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30348)Memory used [KB]: 10746
% 0.22/0.53  % (30348)Time elapsed: 0.115 s
% 0.22/0.53  % (30348)------------------------------
% 0.22/0.53  % (30348)------------------------------
% 0.22/0.53  % (30347)Refutation not found, incomplete strategy% (30347)------------------------------
% 0.22/0.53  % (30347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30347)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30347)Memory used [KB]: 10746
% 0.22/0.53  % (30347)Time elapsed: 0.085 s
% 0.22/0.53  % (30347)------------------------------
% 0.22/0.53  % (30347)------------------------------
% 0.22/0.53  % (30362)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (30352)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (30354)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (30338)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (30362)Refutation not found, incomplete strategy% (30362)------------------------------
% 0.22/0.53  % (30362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30362)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30362)Memory used [KB]: 6268
% 0.22/0.53  % (30362)Time elapsed: 0.117 s
% 0.22/0.53  % (30362)------------------------------
% 0.22/0.53  % (30362)------------------------------
% 0.22/0.53  % (30359)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (30338)Refutation not found, incomplete strategy% (30338)------------------------------
% 0.22/0.53  % (30338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30338)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30338)Memory used [KB]: 10746
% 0.22/0.53  % (30338)Time elapsed: 0.089 s
% 0.22/0.53  % (30338)------------------------------
% 0.22/0.53  % (30338)------------------------------
% 0.22/0.53  % (30364)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (30366)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (30359)Refutation not found, incomplete strategy% (30359)------------------------------
% 0.22/0.53  % (30359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30359)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30359)Memory used [KB]: 10746
% 0.22/0.53  % (30359)Time elapsed: 0.121 s
% 0.22/0.53  % (30359)------------------------------
% 0.22/0.53  % (30359)------------------------------
% 0.22/0.53  % (30354)Refutation not found, incomplete strategy% (30354)------------------------------
% 0.22/0.53  % (30354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30354)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30354)Memory used [KB]: 10618
% 0.22/0.53  % (30354)Time elapsed: 0.109 s
% 0.22/0.53  % (30354)------------------------------
% 0.22/0.53  % (30354)------------------------------
% 0.22/0.53  % (30358)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (30357)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (30351)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (30350)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (30365)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (30344)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (30357)Refutation not found, incomplete strategy% (30357)------------------------------
% 0.22/0.55  % (30357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (30357)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (30357)Memory used [KB]: 11001
% 0.22/0.56  % (30357)Time elapsed: 0.138 s
% 0.22/0.56  % (30357)------------------------------
% 0.22/0.56  % (30357)------------------------------
% 0.22/0.56  % (30358)Refutation not found, incomplete strategy% (30358)------------------------------
% 0.22/0.56  % (30358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (30358)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (30358)Memory used [KB]: 1791
% 0.22/0.56  % (30358)Time elapsed: 0.129 s
% 0.22/0.56  % (30358)------------------------------
% 0.22/0.56  % (30358)------------------------------
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f441,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f440,f147])).
% 0.22/0.56  fof(f147,plain,(
% 0.22/0.56    r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK6))),
% 0.22/0.56    inference(resolution,[],[f146,f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    r4_wellord1(k1_wellord2(sK6),k1_wellord2(sK7))),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    (sK6 != sK7 & r4_wellord1(k1_wellord2(sK6),k1_wellord2(sK7)) & v3_ordinal1(sK7)) & v3_ordinal1(sK6)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f17,f44,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK6 != X1 & r4_wellord1(k1_wellord2(sK6),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK6))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ? [X1] : (sK6 != X1 & r4_wellord1(k1_wellord2(sK6),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK6 != sK7 & r4_wellord1(k1_wellord2(sK6),k1_wellord2(sK7)) & v3_ordinal1(sK7))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.56    inference(flattening,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.56    inference(negated_conjecture,[],[f13])).
% 0.22/0.56  fof(f13,conjecture,(
% 0.22/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.22/0.56  fof(f146,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))) )),
% 0.22/0.56    inference(resolution,[],[f141,f78])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.57  fof(f141,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r4_wellord1(k1_wellord2(X0),X1) | r4_wellord1(X1,k1_wellord2(X0))) )),
% 0.22/0.57    inference(resolution,[],[f80,f78])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | r4_wellord1(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.22/0.57  fof(f440,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK6))),
% 0.22/0.57    inference(backward_demodulation,[],[f416,f435])).
% 0.22/0.57  fof(f435,plain,(
% 0.22/0.57    k1_wellord2(sK6) = k2_wellord1(k1_wellord2(sK7),sK6)),
% 0.22/0.57    inference(resolution,[],[f433,f112])).
% 0.22/0.57  fof(f112,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.57  fof(f433,plain,(
% 0.22/0.57    r1_tarski(sK6,sK7)),
% 0.22/0.57    inference(resolution,[],[f425,f323])).
% 0.22/0.57  fof(f323,plain,(
% 0.22/0.57    sP0(k1_wellord2(sK7),sK6,sK6)),
% 0.22/0.57    inference(subsumption_resolution,[],[f322,f78])).
% 0.22/0.57  fof(f322,plain,(
% 0.22/0.57    sP0(k1_wellord2(sK7),sK6,sK6) | ~v1_relat_1(k1_wellord2(sK7))),
% 0.22/0.57    inference(resolution,[],[f319,f89])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(definition_folding,[],[f22,f35,f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3)))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> sP0(X0,X1,X2)) | ~sP1(X0))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 0.22/0.57  fof(f319,plain,(
% 0.22/0.57    ~sP1(k1_wellord2(sK7)) | sP0(k1_wellord2(sK7),sK6,sK6)),
% 0.22/0.57    inference(superposition,[],[f119,f309])).
% 0.22/0.57  fof(f309,plain,(
% 0.22/0.57    sK6 = k1_wellord1(k1_wellord2(sK7),sK6)),
% 0.22/0.57    inference(subsumption_resolution,[],[f308,f75])).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    v3_ordinal1(sK7)),
% 0.22/0.57    inference(cnf_transformation,[],[f45])).
% 0.22/0.57  fof(f308,plain,(
% 0.22/0.57    sK6 = k1_wellord1(k1_wellord2(sK7),sK6) | ~v3_ordinal1(sK7)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f302])).
% 0.22/0.57  fof(f302,plain,(
% 0.22/0.57    sK6 = k1_wellord1(k1_wellord2(sK7),sK6) | ~v3_ordinal1(sK7) | sK6 = k1_wellord1(k1_wellord2(sK7),sK6)),
% 0.22/0.57    inference(resolution,[],[f301,f168])).
% 0.22/0.57  fof(f168,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(sK6,X0) | ~v3_ordinal1(X0) | sK6 = k1_wellord1(k1_wellord2(X0),sK6)) )),
% 0.22/0.57    inference(resolution,[],[f91,f74])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    v3_ordinal1(sK6)),
% 0.22/0.57    inference(cnf_transformation,[],[f45])).
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | k1_wellord1(k1_wellord2(X1),X0) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.57    inference(flattening,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.22/0.57  fof(f301,plain,(
% 0.22/0.57    r2_hidden(sK6,sK7) | sK6 = k1_wellord1(k1_wellord2(sK7),sK6)),
% 0.22/0.57    inference(resolution,[],[f300,f175])).
% 0.22/0.57  fof(f175,plain,(
% 0.22/0.57    r2_hidden(sK7,sK6) | r2_hidden(sK6,sK7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f173,f77])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    sK6 != sK7),
% 0.22/0.57    inference(cnf_transformation,[],[f45])).
% 0.22/0.57  fof(f173,plain,(
% 0.22/0.57    r2_hidden(sK6,sK7) | sK6 = sK7 | r2_hidden(sK7,sK6)),
% 0.22/0.57    inference(resolution,[],[f170,f75])).
% 0.22/0.57  fof(f170,plain,(
% 0.22/0.57    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK6,X0) | sK6 = X0 | r2_hidden(X0,sK6)) )),
% 0.22/0.57    inference(resolution,[],[f92,f74])).
% 0.22/0.57  fof(f92,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v3_ordinal1(X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | r2_hidden(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.57    inference(flattening,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.57  fof(f300,plain,(
% 0.22/0.57    ~r2_hidden(sK7,sK6) | sK6 = k1_wellord1(k1_wellord2(sK7),sK6)),
% 0.22/0.57    inference(subsumption_resolution,[],[f299,f76])).
% 0.22/0.57  fof(f299,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK6),k1_wellord2(sK7)) | ~r2_hidden(sK7,sK6) | sK6 = k1_wellord1(k1_wellord2(sK7),sK6)),
% 0.22/0.57    inference(superposition,[],[f258,f281])).
% 0.22/0.57  fof(f281,plain,(
% 0.22/0.57    k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7) | sK6 = k1_wellord1(k1_wellord2(sK7),sK6)),
% 0.22/0.57    inference(resolution,[],[f279,f112])).
% 0.22/0.57  fof(f279,plain,(
% 0.22/0.57    r1_tarski(sK7,sK6) | sK6 = k1_wellord1(k1_wellord2(sK7),sK6)),
% 0.22/0.57    inference(subsumption_resolution,[],[f275,f75])).
% 0.22/0.57  fof(f275,plain,(
% 0.22/0.57    r1_tarski(sK7,sK6) | ~v3_ordinal1(sK7) | sK6 = k1_wellord1(k1_wellord2(sK7),sK6)),
% 0.22/0.57    inference(resolution,[],[f274,f168])).
% 0.22/0.57  fof(f274,plain,(
% 0.22/0.57    r2_hidden(sK6,sK7) | r1_tarski(sK7,sK6)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f272])).
% 0.22/0.57  fof(f272,plain,(
% 0.22/0.57    r2_hidden(sK6,sK7) | r1_tarski(sK7,sK6) | r1_tarski(sK7,sK6)),
% 0.22/0.57    inference(resolution,[],[f266,f118])).
% 0.22/0.57  fof(f118,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(sK14(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK14(X0,X1),X1) & r2_hidden(sK14(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f71,f72])).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK14(X0,X1),X1) & r2_hidden(sK14(X0,X1),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f70])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.57  fof(f266,plain,(
% 0.22/0.57    ( ! [X1] : (r2_hidden(sK14(sK7,X1),sK6) | r2_hidden(sK6,sK7) | r1_tarski(sK7,X1)) )),
% 0.22/0.57    inference(resolution,[],[f264,f117])).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(sK14(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f73])).
% 0.22/0.57  fof(f264,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK7) | r2_hidden(X0,sK6) | r2_hidden(sK6,sK7)) )),
% 0.22/0.57    inference(resolution,[],[f254,f175])).
% 0.22/0.57  fof(f254,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(sK7,sK6) | ~r2_hidden(X0,sK7) | r2_hidden(X0,sK6)) )),
% 0.22/0.57    inference(superposition,[],[f196,f253])).
% 0.22/0.57  fof(f253,plain,(
% 0.22/0.57    sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f252,f147])).
% 0.22/0.57  fof(f252,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK6)) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f251])).
% 0.22/0.57  fof(f251,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK6)) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(superposition,[],[f218,f235])).
% 0.22/0.57  fof(f235,plain,(
% 0.22/0.57    k1_wellord2(sK6) = k2_wellord1(k1_wellord2(sK7),sK6) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(resolution,[],[f233,f112])).
% 0.22/0.57  fof(f233,plain,(
% 0.22/0.57    r1_tarski(sK6,sK7) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f230])).
% 0.22/0.57  fof(f230,plain,(
% 0.22/0.57    sK7 = k1_wellord1(k1_wellord2(sK6),sK7) | r1_tarski(sK6,sK7) | r1_tarski(sK6,sK7)),
% 0.22/0.57    inference(resolution,[],[f226,f118])).
% 0.22/0.57  fof(f226,plain,(
% 0.22/0.57    ( ! [X1] : (r2_hidden(sK14(sK6,X1),sK7) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) | r1_tarski(sK6,X1)) )),
% 0.22/0.57    inference(resolution,[],[f223,f117])).
% 0.22/0.57  fof(f223,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK6) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) | r2_hidden(X0,sK7)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f222,f178])).
% 0.22/0.57  fof(f178,plain,(
% 0.22/0.57    r2_hidden(sK6,sK7) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f176,f74])).
% 0.22/0.57  fof(f176,plain,(
% 0.22/0.57    r2_hidden(sK6,sK7) | ~v3_ordinal1(sK6) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(resolution,[],[f175,f169])).
% 0.22/0.57  fof(f169,plain,(
% 0.22/0.57    ( ! [X1] : (~r2_hidden(sK7,X1) | ~v3_ordinal1(X1) | sK7 = k1_wellord1(k1_wellord2(X1),sK7)) )),
% 0.22/0.57    inference(resolution,[],[f91,f75])).
% 0.22/0.57  fof(f222,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK6) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) | ~r2_hidden(sK6,sK7) | r2_hidden(X0,sK7)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f219,f75])).
% 0.22/0.57  fof(f219,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK6) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) | ~r2_hidden(sK6,sK7) | r2_hidden(X0,sK7) | ~v3_ordinal1(sK7)) )),
% 0.22/0.57    inference(resolution,[],[f193,f186])).
% 0.22/0.57  fof(f186,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2) | ~v3_ordinal1(X2)) )),
% 0.22/0.57    inference(resolution,[],[f97,f154])).
% 0.22/0.57  fof(f154,plain,(
% 0.22/0.57    ( ! [X0] : (sP2(X0,k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.57    inference(resolution,[],[f153,f138])).
% 0.22/0.57  fof(f138,plain,(
% 0.22/0.57    ( ! [X0] : (~sP3(k1_wellord2(X0),X0) | sP2(X0,k1_wellord2(X0))) )),
% 0.22/0.57    inference(superposition,[],[f122,f137])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.57    inference(resolution,[],[f136,f104])).
% 0.22/0.57  fof(f104,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~sP4(X0,X1) | k3_relat_1(X0) = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f67])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    ! [X0,X1] : ((sP4(X0,X1) | ((~r1_tarski(sK12(X0,X1),sK13(X0,X1)) | ~r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0)) & (r1_tarski(sK12(X0,X1),sK13(X0,X1)) | r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0)) & r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK12(X0,X1),X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP4(X0,X1)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f65,f66])).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => ((~r1_tarski(sK12(X0,X1),sK13(X0,X1)) | ~r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0)) & (r1_tarski(sK12(X0,X1),sK13(X0,X1)) | r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0)) & r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK12(X0,X1),X1)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    ! [X0,X1] : ((sP4(X0,X1) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP4(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f64])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    ! [X1,X0] : ((sP4(X1,X0) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP4(X1,X0)))),
% 0.22/0.57    inference(flattening,[],[f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ! [X1,X0] : ((sP4(X1,X0) | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP4(X1,X0)))),
% 0.22/0.57    inference(nnf_transformation,[],[f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ! [X1,X0] : (sP4(X1,X0) <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.57  fof(f136,plain,(
% 0.22/0.57    ( ! [X0] : (sP4(k1_wellord2(X0),X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f135,f78])).
% 0.22/0.57  fof(f135,plain,(
% 0.22/0.57    ( ! [X0] : (sP4(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.57    inference(resolution,[],[f123,f111])).
% 0.22/0.57  fof(f111,plain,(
% 0.22/0.57    ( ! [X0,X1] : (sP5(X0,X1) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ! [X0,X1] : (sP5(X0,X1) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(definition_folding,[],[f31,f41,f40])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> sP4(X1,X0)) | ~sP5(X0,X1))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(flattening,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.57  fof(f123,plain,(
% 0.22/0.57    ( ! [X0] : (~sP5(X0,k1_wellord2(X0)) | sP4(k1_wellord2(X0),X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f102])).
% 0.22/0.57  fof(f102,plain,(
% 0.22/0.57    ( ! [X0,X1] : (sP4(X1,X0) | k1_wellord2(X0) != X1 | ~sP5(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ~sP4(X1,X0)) & (sP4(X1,X0) | k1_wellord2(X0) != X1)) | ~sP5(X0,X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f41])).
% 0.22/0.57  fof(f122,plain,(
% 0.22/0.57    ( ! [X0] : (~sP3(X0,k3_relat_1(X0)) | sP2(k3_relat_1(X0),X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f93])).
% 0.22/0.57  fof(f93,plain,(
% 0.22/0.57    ( ! [X0,X1] : (sP2(X1,X0) | k3_relat_1(X0) != X1 | ~sP3(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ! [X0,X1] : ((((k1_wellord1(X0,sK9(X0,X1)) = X1 & r2_hidden(sK9(X0,X1),k3_relat_1(X0))) | k3_relat_1(X0) = X1 | ~sP2(X1,X0)) & (sP2(X1,X0) | (! [X3] : (k1_wellord1(X0,X3) != X1 | ~r2_hidden(X3,k3_relat_1(X0))) & k3_relat_1(X0) != X1))) | ~sP3(X0,X1))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f54,f55])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : (k1_wellord1(X0,X2) = X1 & r2_hidden(X2,k3_relat_1(X0))) => (k1_wellord1(X0,sK9(X0,X1)) = X1 & r2_hidden(sK9(X0,X1),k3_relat_1(X0))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ! [X0,X1] : (((? [X2] : (k1_wellord1(X0,X2) = X1 & r2_hidden(X2,k3_relat_1(X0))) | k3_relat_1(X0) = X1 | ~sP2(X1,X0)) & (sP2(X1,X0) | (! [X3] : (k1_wellord1(X0,X3) != X1 | ~r2_hidden(X3,k3_relat_1(X0))) & k3_relat_1(X0) != X1))) | ~sP3(X0,X1))),
% 0.22/0.57    inference(rectify,[],[f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ! [X1,X0] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ~sP2(X0,X1)) & (sP2(X0,X1) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~sP3(X1,X0))),
% 0.22/0.57    inference(flattening,[],[f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ! [X1,X0] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) | ~sP2(X0,X1)) & (sP2(X0,X1) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~sP3(X1,X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X1,X0] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.57  fof(f153,plain,(
% 0.22/0.57    ( ! [X0] : (sP3(k1_wellord2(X0),X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.57    inference(resolution,[],[f152,f128])).
% 0.22/0.57  fof(f128,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f114])).
% 0.22/0.57  fof(f114,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(flattening,[],[f68])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  fof(f152,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | sP3(k1_wellord2(X1),X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f151,f137])).
% 0.22/0.57  fof(f151,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k3_relat_1(k1_wellord2(X1))) | sP3(k1_wellord2(X1),X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f150,f78])).
% 0.22/0.57  fof(f150,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k3_relat_1(k1_wellord2(X1))) | sP3(k1_wellord2(X1),X0) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.22/0.57    inference(resolution,[],[f101,f90])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v2_wellord1(X1) | ~r1_tarski(X0,k3_relat_1(X1)) | sP3(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X0,X1] : (sP3(X1,X0) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(definition_folding,[],[f29,f38,f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ! [X0,X1] : (sP2(X0,X1) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(flattening,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | (~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X3] : (r2_hidden(X3,X0) => ! [X4] : (r2_hidden(k4_tarski(X4,X3),X1) => r2_hidden(X4,X0))))))),
% 0.22/0.57    inference(rectify,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X2] : (r2_hidden(X2,X0) => ! [X3] : (r2_hidden(k4_tarski(X3,X2),X1) => r2_hidden(X3,X0))))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    ( ! [X4,X0,X5,X1] : (~sP2(X0,X1) | ~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(X4,X0) | r2_hidden(X5,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ! [X0,X1] : ((sP2(X0,X1) | ((~r2_hidden(sK11(X0,X1),X0) & r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X1)) & r2_hidden(sK10(X0,X1),X0))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r2_hidden(k4_tarski(X5,X4),X1)) | ~r2_hidden(X4,X0)) | ~sP2(X0,X1)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f58,f60,f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(k4_tarski(X3,X2),X1)) & r2_hidden(X2,X0)) => (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(k4_tarski(X3,sK10(X0,X1)),X1)) & r2_hidden(sK10(X0,X1),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(k4_tarski(X3,sK10(X0,X1)),X1)) => (~r2_hidden(sK11(X0,X1),X0) & r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X1)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(k4_tarski(X3,X2),X1)) & r2_hidden(X2,X0))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r2_hidden(k4_tarski(X5,X4),X1)) | ~r2_hidden(X4,X0)) | ~sP2(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f57])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    ! [X0,X1] : ((sP2(X0,X1) | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | ~sP2(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f37])).
% 0.22/0.57  fof(f193,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK6),k1_wellord2(sK7)) | ~r2_hidden(X0,sK6) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)) )),
% 0.22/0.57    inference(resolution,[],[f191,f84])).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(k4_tarski(X4,X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0) | sK8(X0,X1,X2) = X1 | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0) & sK8(X0,X1,X2) != X1) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0) | sK8(X0,X1,X2) = X1 | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0) & sK8(X0,X1,X2) != X1) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.57    inference(rectify,[],[f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.57    inference(flattening,[],[f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.57    inference(nnf_transformation,[],[f34])).
% 0.22/0.57  fof(f191,plain,(
% 0.22/0.57    sP0(k1_wellord2(sK7),sK6,sK6) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f190,f78])).
% 0.22/0.57  fof(f190,plain,(
% 0.22/0.57    sP0(k1_wellord2(sK7),sK6,sK6) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7) | ~v1_relat_1(k1_wellord2(sK7))),
% 0.22/0.57    inference(resolution,[],[f185,f89])).
% 0.22/0.57  fof(f185,plain,(
% 0.22/0.57    ~sP1(k1_wellord2(sK7)) | sP0(k1_wellord2(sK7),sK6,sK6) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(superposition,[],[f119,f181])).
% 0.22/0.57  fof(f181,plain,(
% 0.22/0.57    sK6 = k1_wellord1(k1_wellord2(sK7),sK6) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f179,f75])).
% 0.22/0.57  fof(f179,plain,(
% 0.22/0.57    sK7 = k1_wellord1(k1_wellord2(sK6),sK7) | ~v3_ordinal1(sK7) | sK6 = k1_wellord1(k1_wellord2(sK7),sK6)),
% 0.22/0.57    inference(resolution,[],[f178,f168])).
% 0.22/0.57  fof(f218,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6)) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f217,f178])).
% 0.22/0.57  fof(f217,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6)) | ~r2_hidden(sK6,sK7) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f216,f75])).
% 0.22/0.57  fof(f216,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6)) | ~r2_hidden(sK6,sK7) | ~v3_ordinal1(sK7) | sK7 = k1_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(superposition,[],[f213,f181])).
% 0.22/0.57  fof(f213,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f212,f137])).
% 0.22/0.57  fof(f212,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v3_ordinal1(X1)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f211,f78])).
% 0.22/0.57  fof(f211,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.22/0.57    inference(resolution,[],[f79,f90])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.22/0.57  fof(f196,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k1_wellord1(k1_wellord2(sK6),X1)) | ~r2_hidden(X1,sK6) | r2_hidden(X0,sK6)) )),
% 0.22/0.57    inference(resolution,[],[f194,f74])).
% 0.22/0.57  fof(f194,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v3_ordinal1(X1) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,k1_wellord1(k1_wellord2(X1),X0))) )),
% 0.22/0.57    inference(resolution,[],[f186,f166])).
% 0.22/0.57  fof(f166,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) | ~r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X2))) )),
% 0.22/0.57    inference(resolution,[],[f165,f78])).
% 0.22/0.57  fof(f165,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.57    inference(resolution,[],[f161,f89])).
% 0.22/0.57  fof(f161,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~sP1(X1) | r2_hidden(k4_tarski(X0,X2),X1) | ~r2_hidden(X0,k1_wellord1(X1,X2))) )),
% 0.22/0.57    inference(resolution,[],[f84,f119])).
% 0.22/0.57  fof(f258,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK6),k2_wellord1(k1_wellord2(sK6),sK7)) | ~r2_hidden(sK7,sK6)),
% 0.22/0.57    inference(subsumption_resolution,[],[f255,f74])).
% 0.22/0.57  fof(f255,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK6),k2_wellord1(k1_wellord2(sK6),sK7)) | ~r2_hidden(sK7,sK6) | ~v3_ordinal1(sK6)),
% 0.22/0.57    inference(superposition,[],[f213,f253])).
% 0.22/0.57  fof(f119,plain,(
% 0.22/0.57    ( ! [X0,X1] : (sP0(X0,X1,k1_wellord1(X0,X1)) | ~sP1(X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f81])).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_wellord1(X0,X1) != X2 | ~sP1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | k1_wellord1(X0,X1) != X2)) | ~sP1(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f35])).
% 0.22/0.57  fof(f425,plain,(
% 0.22/0.57    ( ! [X0] : (~sP0(X0,sK6,sK6) | r1_tarski(sK6,sK7)) )),
% 0.22/0.57    inference(resolution,[],[f418,f120])).
% 0.22/0.57  fof(f120,plain,(
% 0.22/0.57    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | ~sP0(X0,X4,X2)) )),
% 0.22/0.57    inference(equality_resolution,[],[f83])).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f51])).
% 0.22/0.57  fof(f418,plain,(
% 0.22/0.57    r2_hidden(sK6,sK6) | r1_tarski(sK6,sK7)),
% 0.22/0.57    inference(resolution,[],[f413,f347])).
% 0.22/0.57  fof(f347,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK7) | r1_tarski(sK6,sK7) | r2_hidden(X0,sK6)) )),
% 0.22/0.57    inference(resolution,[],[f344,f116])).
% 0.22/0.57  fof(f116,plain,(
% 0.22/0.57    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f73])).
% 0.22/0.57  fof(f344,plain,(
% 0.22/0.57    r1_tarski(sK7,sK6) | r1_tarski(sK6,sK7)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f340])).
% 0.22/0.57  fof(f340,plain,(
% 0.22/0.57    r1_tarski(sK6,sK7) | r1_tarski(sK7,sK6) | r1_tarski(sK6,sK7)),
% 0.22/0.57    inference(resolution,[],[f315,f118])).
% 0.22/0.57  fof(f315,plain,(
% 0.22/0.57    ( ! [X1] : (r2_hidden(sK14(sK6,X1),sK7) | r1_tarski(sK6,X1) | r1_tarski(sK7,sK6)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f312,f309])).
% 0.22/0.57  fof(f312,plain,(
% 0.22/0.57    ( ! [X1] : (r2_hidden(sK14(sK6,X1),sK7) | r1_tarski(sK7,sK6) | r1_tarski(k1_wellord1(k1_wellord2(sK7),sK6),X1)) )),
% 0.22/0.57    inference(backward_demodulation,[],[f293,f309])).
% 0.22/0.57  fof(f293,plain,(
% 0.22/0.57    ( ! [X1] : (r2_hidden(sK14(k1_wellord1(k1_wellord2(sK7),sK6),X1),sK7) | r1_tarski(sK7,sK6) | r1_tarski(k1_wellord1(k1_wellord2(sK7),sK6),X1)) )),
% 0.22/0.57    inference(resolution,[],[f277,f117])).
% 0.22/0.57  fof(f277,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k1_wellord1(k1_wellord2(sK7),sK6)) | r2_hidden(X0,sK7) | r1_tarski(sK7,sK6)) )),
% 0.22/0.57    inference(resolution,[],[f274,f197])).
% 0.22/0.57  fof(f197,plain,(
% 0.22/0.57    ( ! [X2,X3] : (~r2_hidden(X3,sK7) | r2_hidden(X2,sK7) | ~r2_hidden(X2,k1_wellord1(k1_wellord2(sK7),X3))) )),
% 0.22/0.57    inference(resolution,[],[f194,f75])).
% 0.22/0.57  fof(f413,plain,(
% 0.22/0.57    r2_hidden(sK6,sK7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f175,f412])).
% 0.22/0.57  fof(f412,plain,(
% 0.22/0.57    ~r2_hidden(sK7,sK6)),
% 0.22/0.57    inference(subsumption_resolution,[],[f411,f76])).
% 0.22/0.57  fof(f411,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK6),k1_wellord2(sK7)) | ~r2_hidden(sK7,sK6)),
% 0.22/0.57    inference(backward_demodulation,[],[f258,f410])).
% 0.22/0.57  fof(f410,plain,(
% 0.22/0.57    k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f409,f112])).
% 0.22/0.57  fof(f409,plain,(
% 0.22/0.57    k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7) | r1_tarski(sK7,sK6)),
% 0.22/0.57    inference(resolution,[],[f408,f274])).
% 0.22/0.57  fof(f408,plain,(
% 0.22/0.57    ~r2_hidden(sK6,sK7) | k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f407,f147])).
% 0.22/0.57  fof(f407,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK6)) | ~r2_hidden(sK6,sK7) | k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(superposition,[],[f320,f363])).
% 0.22/0.57  fof(f363,plain,(
% 0.22/0.57    k1_wellord2(sK6) = k2_wellord1(k1_wellord2(sK7),sK6) | k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(resolution,[],[f346,f112])).
% 0.22/0.57  fof(f346,plain,(
% 0.22/0.57    r1_tarski(sK6,sK7) | k1_wellord2(sK7) = k2_wellord1(k1_wellord2(sK6),sK7)),
% 0.22/0.57    inference(resolution,[],[f344,f112])).
% 0.22/0.57  fof(f320,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6)) | ~r2_hidden(sK6,sK7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f317,f75])).
% 0.22/0.57  fof(f317,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6)) | ~r2_hidden(sK6,sK7) | ~v3_ordinal1(sK7)),
% 0.22/0.57    inference(superposition,[],[f213,f309])).
% 0.22/0.57  fof(f416,plain,(
% 0.22/0.57    ~r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK6))),
% 0.22/0.57    inference(subsumption_resolution,[],[f320,f413])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (30344)------------------------------
% 0.22/0.57  % (30344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (30344)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (30344)Memory used [KB]: 6524
% 0.22/0.57  % (30344)Time elapsed: 0.135 s
% 0.22/0.57  % (30344)------------------------------
% 0.22/0.57  % (30344)------------------------------
% 0.22/0.57  % (30335)Success in time 0.196 s
%------------------------------------------------------------------------------
