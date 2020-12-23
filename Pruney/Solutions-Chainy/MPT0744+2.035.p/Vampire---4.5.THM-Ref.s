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
% DateTime   : Thu Dec  3 12:55:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 202 expanded)
%              Number of leaves         :   17 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  297 ( 815 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f67,f95,f102,f137,f144,f152,f170])).

fof(f170,plain,
    ( spl2_1
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f162,f52])).

fof(f52,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f35,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f162,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl2_1
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f61,f94])).

% (1800)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f94,plain,
    ( sK0 = sK1
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f61,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_1
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f152,plain,
    ( spl2_2
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f150,f145])).

fof(f145,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f124,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f124,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl2_5
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f150,plain,
    ( r1_tarski(sK1,sK0)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f149,f32])).

fof(f32,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK0,X1)
            | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK0,X1)
            | r2_hidden(sK0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK0,X1)
          | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK0,X1)
          | r2_hidden(sK0,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK0,sK1)
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( r1_ordinal1(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f149,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK1,sK0)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f147,f31])).

fof(f31,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f147,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | r1_tarski(sK1,sK0)
    | spl2_2 ),
    inference(resolution,[],[f82,f65])).

fof(f65,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_2
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f82,plain,(
    ! [X2,X3] :
      ( r1_ordinal1(X3,X2)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r1_tarski(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r1_ordinal1(X3,X2)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X3) ) ),
    inference(resolution,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f144,plain,
    ( spl2_4
    | spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f142,f59,f122,f92])).

fof(f142,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ spl2_1 ),
    inference(resolution,[],[f60,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f46,f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f60,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f137,plain,
    ( spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f135,f31])).

fof(f135,plain,
    ( ~ v3_ordinal1(sK0)
    | spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f128,f76])).

fof(f76,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(factoring,[],[f40])).

fof(f128,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | spl2_2
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f65,f94])).

fof(f102,plain,
    ( spl2_1
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f100,f68])).

fof(f68,plain,(
    v1_ordinal1(sK0) ),
    inference(resolution,[],[f38,f31])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f100,plain,
    ( ~ v1_ordinal1(sK0)
    | spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f99,f32])).

fof(f99,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK0)
    | spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f97,f73])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(resolution,[],[f54,f61])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f90,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f90,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_3
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f95,plain,
    ( spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f86,f63,f92,f88])).

fof(f86,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f85,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f85,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f84,f31])).

fof(f84,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f77,f32])).

fof(f77,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f41,f64])).

fof(f64,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f67,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f51,f63,f59])).

fof(f51,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f50,f63,f59])).

fof(f50,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f34,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (1789)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (1783)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (1807)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (1789)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (1798)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (1788)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (1793)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (1797)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f66,f67,f95,f102,f137,f144,f152,f170])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    spl2_1 | ~spl2_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f169])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    $false | (spl2_1 | ~spl2_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f162,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f35,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) | (spl2_1 | ~spl2_4)),
% 0.20/0.51    inference(backward_demodulation,[],[f61,f94])).
% 0.20/0.51  % (1800)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    sK0 = sK1 | ~spl2_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl2_4 <=> sK0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | spl2_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl2_1 <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    spl2_2 | ~spl2_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f151])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    $false | (spl2_2 | ~spl2_5)),
% 0.20/0.51    inference(subsumption_resolution,[],[f150,f145])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    ~r1_tarski(sK1,sK0) | ~spl2_5),
% 0.20/0.51    inference(resolution,[],[f124,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    r2_hidden(sK0,sK1) | ~spl2_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f122])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl2_5 <=> r2_hidden(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    r1_tarski(sK1,sK0) | spl2_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f149,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    v3_ordinal1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    ~v3_ordinal1(sK1) | r1_tarski(sK1,sK0) | spl2_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f147,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    v3_ordinal1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | r1_tarski(sK1,sK0) | spl2_2),
% 0.20/0.51    inference(resolution,[],[f82,f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ~r1_ordinal1(sK0,sK1) | spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    spl2_2 <=> r1_ordinal1(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X2,X3] : (r1_ordinal1(X3,X2) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r1_tarski(X2,X3)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r1_ordinal1(X3,X2) | ~v3_ordinal1(X2) | ~v3_ordinal1(X3)) )),
% 0.20/0.51    inference(resolution,[],[f41,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    spl2_4 | spl2_5 | ~spl2_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f142,f59,f122,f92])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    r2_hidden(sK0,sK1) | sK0 = sK1 | ~spl2_1),
% 0.20/0.51    inference(resolution,[],[f60,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.20/0.51    inference(definition_unfolding,[],[f46,f36])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.51    inference(flattening,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl2_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f59])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    spl2_2 | ~spl2_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f136])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    $false | (spl2_2 | ~spl2_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f135,f31])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ~v3_ordinal1(sK0) | (spl2_2 | ~spl2_4)),
% 0.20/0.51    inference(resolution,[],[f128,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X0] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(factoring,[],[f40])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    ~r1_ordinal1(sK0,sK0) | (spl2_2 | ~spl2_4)),
% 0.20/0.51    inference(backward_demodulation,[],[f65,f94])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    spl2_1 | ~spl2_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    $false | (spl2_1 | ~spl2_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f100,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    v1_ordinal1(sK0)),
% 0.20/0.51    inference(resolution,[],[f38,f31])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ~v1_ordinal1(sK0) | (spl2_1 | ~spl2_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f99,f32])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ~v3_ordinal1(sK1) | ~v1_ordinal1(sK0) | (spl2_1 | ~spl2_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f97,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK1) | spl2_1),
% 0.20/0.51    inference(resolution,[],[f54,f61])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f47,f36])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v1_ordinal1(sK0) | ~spl2_3),
% 0.20/0.51    inference(resolution,[],[f90,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    r2_xboole_0(sK0,sK1) | ~spl2_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl2_3 <=> r2_xboole_0(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl2_3 | spl2_4 | ~spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f86,f63,f92,f88])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    sK0 = sK1 | r2_xboole_0(sK0,sK1) | ~spl2_2),
% 0.20/0.51    inference(resolution,[],[f85,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | ~spl2_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f84,f31])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl2_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f77,f32])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl2_2),
% 0.20/0.51    inference(resolution,[],[f41,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    r1_ordinal1(sK0,sK1) | ~spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f63])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    spl2_1 | spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f51,f63,f59])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.20/0.51    inference(definition_unfolding,[],[f33,f36])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ~spl2_1 | ~spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f63,f59])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.20/0.51    inference(definition_unfolding,[],[f34,f36])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (1789)------------------------------
% 0.20/0.51  % (1789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1789)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (1789)Memory used [KB]: 10746
% 0.20/0.51  % (1789)Time elapsed: 0.099 s
% 0.20/0.51  % (1789)------------------------------
% 0.20/0.51  % (1789)------------------------------
% 0.20/0.51  % (1782)Success in time 0.156 s
%------------------------------------------------------------------------------
