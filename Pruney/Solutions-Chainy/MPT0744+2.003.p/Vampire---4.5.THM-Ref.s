%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 150 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :  256 ( 393 expanded)
%              Number of equality atoms :    8 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f64,f103,f107,f121,f146,f184,f196,f213,f233,f235,f238,f248])).

fof(f248,plain,(
    spl2_15 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl2_15 ),
    inference(unit_resulting_resolution,[],[f30,f195,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f33,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f195,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl2_15
  <=> v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f30,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f238,plain,
    ( ~ spl2_13
    | spl2_14
    | ~ spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f236,f94,f98,f178,f174])).

fof(f174,plain,
    ( spl2_13
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f178,plain,
    ( spl2_14
  <=> ! [X9] :
        ( ~ v3_ordinal1(X9)
        | r2_hidden(sK0,X9)
        | ~ r2_hidden(sK1,X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f98,plain,
    ( spl2_5
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f94,plain,
    ( spl2_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(sK1)
        | ~ v3_ordinal1(X0)
        | ~ v1_ordinal1(sK0)
        | ~ r2_hidden(sK1,X0)
        | r2_hidden(sK0,X0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f96,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X2)
      | ~ v1_ordinal1(X0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

fof(f96,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f235,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f234,f60,f98,f94,f90])).

fof(f90,plain,
    ( spl2_3
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f60,plain,
    ( spl2_2
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f234,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f61,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f61,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f233,plain,
    ( spl2_2
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl2_2
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f31,f215,f81])).

fof(f81,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(factoring,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f215,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | spl2_2
    | ~ spl2_10 ),
    inference(superposition,[],[f62,f145])).

fof(f145,plain,
    ( sK0 = sK1
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl2_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f62,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f31,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f213,plain,
    ( ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f129,f141])).

fof(f141,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl2_9
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f129,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl2_7 ),
    inference(resolution,[],[f120,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f120,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl2_7
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f196,plain,
    ( ~ spl2_15
    | spl2_1
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f189,f178,f56,f193])).

fof(f56,plain,
    ( spl2_1
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f189,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl2_14 ),
    inference(resolution,[],[f179,f49])).

fof(f49,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f32,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f179,plain,
    ( ! [X9] :
        ( ~ r2_hidden(sK1,X9)
        | r2_hidden(sK0,X9)
        | ~ v3_ordinal1(X9) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f178])).

fof(f184,plain,(
    spl2_13 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl2_13 ),
    inference(subsumption_resolution,[],[f66,f176])).

fof(f176,plain,
    ( ~ v1_ordinal1(sK0)
    | spl2_13 ),
    inference(avatar_component_clause,[],[f174])).

fof(f66,plain,(
    v1_ordinal1(sK0) ),
    inference(resolution,[],[f36,f31])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f146,plain,
    ( spl2_9
    | spl2_10
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f137,f56,f143,f139])).

fof(f137,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f53,f57])).

fof(f57,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 = X1
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f121,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_5
    | spl2_2 ),
    inference(avatar_split_clause,[],[f111,f60,f98,f90,f118])).

fof(f111,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | spl2_2 ),
    inference(resolution,[],[f62,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f107,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f30,f100])).

fof(f100,plain,
    ( ~ v3_ordinal1(sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f103,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f31,f92])).

fof(f92,plain,
    ( ~ v3_ordinal1(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f64,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f48,f60,f56])).

fof(f48,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f28,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f47,f60,f56])).

fof(f47,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f29,f33])).

% (8385)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (8384)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (8388)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% (8389)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (8411)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f29,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:25:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (8394)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.49  % (8394)Refutation not found, incomplete strategy% (8394)------------------------------
% 0.21/0.49  % (8394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8408)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.49  % (8394)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (8394)Memory used [KB]: 10746
% 0.21/0.49  % (8394)Time elapsed: 0.066 s
% 0.21/0.49  % (8394)------------------------------
% 0.21/0.49  % (8394)------------------------------
% 0.21/0.52  % (8396)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (8387)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (8397)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (8397)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f249,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f63,f64,f103,f107,f121,f146,f184,f196,f213,f233,f235,f238,f248])).
% 0.21/0.55  fof(f248,plain,(
% 0.21/0.55    spl2_15),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f246])).
% 0.21/0.55  fof(f246,plain,(
% 0.21/0.55    $false | spl2_15),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f30,f195,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f35,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.55  fof(f195,plain,(
% 0.21/0.55    ~v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | spl2_15),
% 0.21/0.55    inference(avatar_component_clause,[],[f193])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    spl2_15 <=> v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    v3_ordinal1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.55    inference(negated_conjecture,[],[f12])).
% 0.21/0.55  fof(f12,conjecture,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.21/0.55  fof(f238,plain,(
% 0.21/0.55    ~spl2_13 | spl2_14 | ~spl2_5 | ~spl2_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f236,f94,f98,f178,f174])).
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    spl2_13 <=> v1_ordinal1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    spl2_14 <=> ! [X9] : (~v3_ordinal1(X9) | r2_hidden(sK0,X9) | ~r2_hidden(sK1,X9))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    spl2_5 <=> v3_ordinal1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    spl2_4 <=> r1_tarski(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    ( ! [X0] : (~v3_ordinal1(sK1) | ~v3_ordinal1(X0) | ~v1_ordinal1(sK0) | ~r2_hidden(sK1,X0) | r2_hidden(sK0,X0)) ) | ~spl2_4),
% 0.21/0.55    inference(resolution,[],[f96,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X2) | ~v1_ordinal1(X0) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X0,X2) | (~r2_hidden(X1,X2) | ~r1_tarski(X0,X1))) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    r1_tarski(sK0,sK1) | ~spl2_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f94])).
% 0.21/0.55  fof(f235,plain,(
% 0.21/0.55    ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f234,f60,f98,f94,f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    spl2_3 <=> v3_ordinal1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    spl2_2 <=> r1_ordinal1(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.55  fof(f234,plain,(
% 0.21/0.55    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl2_2),
% 0.21/0.55    inference(resolution,[],[f61,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    r1_ordinal1(sK0,sK1) | ~spl2_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f60])).
% 0.21/0.55  fof(f233,plain,(
% 0.21/0.55    spl2_2 | ~spl2_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f225])).
% 0.21/0.55  fof(f225,plain,(
% 0.21/0.55    $false | (spl2_2 | ~spl2_10)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f31,f215,f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X0] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X0] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(factoring,[],[f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.55  fof(f215,plain,(
% 0.21/0.55    ~r1_ordinal1(sK0,sK0) | (spl2_2 | ~spl2_10)),
% 0.21/0.55    inference(superposition,[],[f62,f145])).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    sK0 = sK1 | ~spl2_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f143])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    spl2_10 <=> sK0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ~r1_ordinal1(sK0,sK1) | spl2_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f60])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    v3_ordinal1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    ~spl2_7 | ~spl2_9),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    $false | (~spl2_7 | ~spl2_9)),
% 0.21/0.55    inference(subsumption_resolution,[],[f129,f141])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1) | ~spl2_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f139])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    spl2_9 <=> r2_hidden(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ~r2_hidden(sK0,sK1) | ~spl2_7),
% 0.21/0.55    inference(resolution,[],[f120,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    r2_hidden(sK1,sK0) | ~spl2_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f118])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    spl2_7 <=> r2_hidden(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    ~spl2_15 | spl2_1 | ~spl2_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f189,f178,f56,f193])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    spl2_1 <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl2_14),
% 0.21/0.55    inference(resolution,[],[f179,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f32,f33])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.21/0.55  fof(f179,plain,(
% 0.21/0.55    ( ! [X9] : (~r2_hidden(sK1,X9) | r2_hidden(sK0,X9) | ~v3_ordinal1(X9)) ) | ~spl2_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f178])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    spl2_13),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.55  fof(f181,plain,(
% 0.21/0.55    $false | spl2_13),
% 0.21/0.55    inference(subsumption_resolution,[],[f66,f176])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    ~v1_ordinal1(sK0) | spl2_13),
% 0.21/0.55    inference(avatar_component_clause,[],[f174])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    v1_ordinal1(sK0)),
% 0.21/0.55    inference(resolution,[],[f36,f31])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    spl2_9 | spl2_10 | ~spl2_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f137,f56,f143,f139])).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    sK0 = sK1 | r2_hidden(sK0,sK1) | ~spl2_1),
% 0.21/0.55    inference(resolution,[],[f53,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl2_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f56])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 = X1 | r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f44,f33])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    spl2_7 | ~spl2_3 | ~spl2_5 | spl2_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f111,f60,f98,f90,f118])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | spl2_2),
% 0.21/0.55    inference(resolution,[],[f62,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    spl2_5),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f106])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    $false | spl2_5),
% 0.21/0.55    inference(subsumption_resolution,[],[f30,f100])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ~v3_ordinal1(sK1) | spl2_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f98])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    spl2_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    $false | spl2_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f31,f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    ~v3_ordinal1(sK0) | spl2_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f90])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    spl2_1 | spl2_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f48,f60,f56])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.21/0.55    inference(definition_unfolding,[],[f28,f33])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ~spl2_1 | ~spl2_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f47,f60,f56])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.21/0.55    inference(definition_unfolding,[],[f29,f33])).
% 0.21/0.55  % (8385)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (8384)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.41/0.56  % (8388)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.41/0.56  % (8389)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.41/0.56  % (8411)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.41/0.56  fof(f29,plain,(
% 1.41/0.56    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.41/0.56    inference(cnf_transformation,[],[f14])).
% 1.41/0.56  % SZS output end Proof for theBenchmark
% 1.41/0.56  % (8397)------------------------------
% 1.41/0.56  % (8397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (8397)Termination reason: Refutation
% 1.41/0.56  
% 1.41/0.56  % (8397)Memory used [KB]: 6268
% 1.41/0.56  % (8397)Time elapsed: 0.118 s
% 1.41/0.56  % (8397)------------------------------
% 1.41/0.56  % (8397)------------------------------
% 1.41/0.56  % (8411)Refutation not found, incomplete strategy% (8411)------------------------------
% 1.41/0.56  % (8411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (8411)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (8411)Memory used [KB]: 6140
% 1.41/0.56  % (8411)Time elapsed: 0.133 s
% 1.41/0.56  % (8411)------------------------------
% 1.41/0.56  % (8411)------------------------------
% 1.41/0.57  % (8383)Success in time 0.202 s
%------------------------------------------------------------------------------
