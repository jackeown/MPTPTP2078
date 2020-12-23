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
% DateTime   : Thu Dec  3 12:55:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 155 expanded)
%              Number of leaves         :   16 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 ( 435 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f51,f58,f63,f108,f163,f226,f289,f357])).

fof(f357,plain,
    ( spl2_2
    | spl2_5
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | spl2_2
    | spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f355,f103])).

fof(f103,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_5
  <=> r2_hidden(sK1,k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f355,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f354,f106])).

fof(f106,plain,
    ( v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_6
  <=> v3_ordinal1(k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f354,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | r2_hidden(sK1,k1_ordinal1(sK0))
    | spl2_2 ),
    inference(resolution,[],[f81,f49])).

fof(f49,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_2
  <=> r1_ordinal1(k1_ordinal1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f81,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,sK1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f31,f27])).

fof(f27,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f289,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f271,f114])).

fof(f114,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f111,f28])).

fof(f28,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f111,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ r2_hidden(sK0,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f94,f65])).

fof(f65,plain,
    ( r1_ordinal1(sK0,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f57,f28])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_ordinal1(X0,X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_4
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_ordinal1(X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f94,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(X1,sK0)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(resolution,[],[f88,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f88,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK0)
      | ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X1,sK0) ) ),
    inference(resolution,[],[f36,f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

% (11021)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f271,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f44,f269])).

fof(f269,plain,
    ( sK0 = sK1
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f267,f266])).

fof(f266,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f44,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f267,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f102,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | X0 = X1
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f102,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f226,plain,
    ( spl2_1
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl2_1
    | spl2_5 ),
    inference(subsumption_resolution,[],[f212,f29])).

fof(f29,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f212,plain,
    ( ~ r2_hidden(sK0,k1_ordinal1(sK0))
    | spl2_1
    | spl2_5 ),
    inference(backward_demodulation,[],[f103,f203])).

fof(f203,plain,
    ( sK0 = sK1
    | spl2_1
    | spl2_5 ),
    inference(subsumption_resolution,[],[f202,f110])).

fof(f110,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_5 ),
    inference(resolution,[],[f103,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f202,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f198,f45])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f198,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f193,f28])).

fof(f193,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(X0,sK1)
      | sK1 = X0
      | r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f32,f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f163,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl2_6 ),
    inference(subsumption_resolution,[],[f161,f28])).

fof(f161,plain,
    ( ~ v3_ordinal1(sK0)
    | spl2_6 ),
    inference(resolution,[],[f107,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(f107,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f108,plain,
    ( ~ spl2_5
    | ~ spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f96,f47,f105,f101])).

fof(f96,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f91,f48])).

fof(f48,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f91,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(X1,sK1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(sK1,X1) ) ),
    inference(resolution,[],[f87,f40])).

fof(f87,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK1)
      | ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(X0,sK1) ) ),
    inference(resolution,[],[f36,f27])).

fof(f63,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f27,f54])).

fof(f54,plain,
    ( ! [X1] : ~ v3_ordinal1(X1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_3
  <=> ! [X1] : ~ v3_ordinal1(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

% (11021)Refutation not found, incomplete strategy% (11021)------------------------------
% (11021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11021)Termination reason: Refutation not found, incomplete strategy

% (11021)Memory used [KB]: 10618
% (11021)Time elapsed: 0.073 s
% (11021)------------------------------
% (11021)------------------------------
fof(f58,plain,
    ( spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f34,f56,f53])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).

fof(f51,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f25,f47,f43])).

fof(f25,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f26,f47,f43])).

fof(f26,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:52:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (11037)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.47  % (11029)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (11037)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (11026)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.50  % (11026)Refutation not found, incomplete strategy% (11026)------------------------------
% 0.22/0.50  % (11026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11026)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (11026)Memory used [KB]: 10618
% 0.22/0.50  % (11026)Time elapsed: 0.083 s
% 0.22/0.50  % (11026)------------------------------
% 0.22/0.50  % (11026)------------------------------
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f358,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f50,f51,f58,f63,f108,f163,f226,f289,f357])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    spl2_2 | spl2_5 | ~spl2_6),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f356])).
% 0.22/0.50  fof(f356,plain,(
% 0.22/0.50    $false | (spl2_2 | spl2_5 | ~spl2_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f355,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ~r2_hidden(sK1,k1_ordinal1(sK0)) | spl2_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl2_5 <=> r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.50  fof(f355,plain,(
% 0.22/0.50    r2_hidden(sK1,k1_ordinal1(sK0)) | (spl2_2 | ~spl2_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f354,f106])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    v3_ordinal1(k1_ordinal1(sK0)) | ~spl2_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f105])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl2_6 <=> v3_ordinal1(k1_ordinal1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.50  fof(f354,plain,(
% 0.22/0.50    ~v3_ordinal1(k1_ordinal1(sK0)) | r2_hidden(sK1,k1_ordinal1(sK0)) | spl2_2),
% 0.22/0.50    inference(resolution,[],[f81,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    spl2_2 <=> r1_ordinal1(k1_ordinal1(sK0),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X0] : (r1_ordinal1(X0,sK1) | ~v3_ordinal1(X0) | r2_hidden(sK1,X0)) )),
% 0.22/0.50    inference(resolution,[],[f31,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    v3_ordinal1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    ~spl2_1 | ~spl2_4 | ~spl2_5),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f288])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    $false | (~spl2_1 | ~spl2_4 | ~spl2_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f271,f114])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ~r2_hidden(sK0,sK0) | ~spl2_4),
% 0.22/0.50    inference(subsumption_resolution,[],[f111,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    v3_ordinal1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ~v3_ordinal1(sK0) | ~r2_hidden(sK0,sK0) | ~spl2_4),
% 0.22/0.50    inference(resolution,[],[f94,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    r1_ordinal1(sK0,sK0) | ~spl2_4),
% 0.22/0.50    inference(resolution,[],[f57,f28])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(X0,X0)) ) | ~spl2_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl2_4 <=> ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(X0,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X1] : (~r1_ordinal1(X1,sK0) | ~v3_ordinal1(X1) | ~r2_hidden(sK0,X1)) )),
% 0.22/0.50    inference(resolution,[],[f88,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,sK0) | ~v3_ordinal1(X1) | ~r1_ordinal1(X1,sK0)) )),
% 0.22/0.50    inference(resolution,[],[f36,f28])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  % (11021)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    r2_hidden(sK0,sK0) | (~spl2_1 | ~spl2_5)),
% 0.22/0.50    inference(backward_demodulation,[],[f44,f269])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    sK0 = sK1 | (~spl2_1 | ~spl2_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f267,f266])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    ~r2_hidden(sK1,sK0) | ~spl2_1),
% 0.22/0.50    inference(resolution,[],[f44,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    sK0 = sK1 | r2_hidden(sK1,sK0) | ~spl2_5),
% 0.22/0.50    inference(resolution,[],[f102,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | X0 = X1 | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    r2_hidden(sK1,k1_ordinal1(sK0)) | ~spl2_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    spl2_1 | spl2_5),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f225])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    $false | (spl2_1 | spl2_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f212,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ~r2_hidden(sK0,k1_ordinal1(sK0)) | (spl2_1 | spl2_5)),
% 0.22/0.50    inference(backward_demodulation,[],[f103,f203])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    sK0 = sK1 | (spl2_1 | spl2_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f202,f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ~r2_hidden(sK1,sK0) | spl2_5),
% 0.22/0.50    inference(resolution,[],[f103,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    sK0 = sK1 | r2_hidden(sK1,sK0) | spl2_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f198,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ~r2_hidden(sK0,sK1) | spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f43])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    r2_hidden(sK0,sK1) | sK0 = sK1 | r2_hidden(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f193,f28])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK1) | sK1 = X0 | r2_hidden(sK1,X0)) )),
% 0.22/0.50    inference(resolution,[],[f32,f27])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl2_6),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    $false | spl2_6),
% 0.22/0.50    inference(subsumption_resolution,[],[f161,f28])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ~v3_ordinal1(sK0) | spl2_6),
% 0.22/0.50    inference(resolution,[],[f107,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => (v3_ordinal1(k1_ordinal1(X0)) & ~v1_xboole_0(k1_ordinal1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    ~v3_ordinal1(k1_ordinal1(sK0)) | spl2_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f105])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ~spl2_5 | ~spl2_6 | ~spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f96,f47,f105,f101])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ~v3_ordinal1(k1_ordinal1(sK0)) | ~r2_hidden(sK1,k1_ordinal1(sK0)) | ~spl2_2),
% 0.22/0.50    inference(resolution,[],[f91,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    r1_ordinal1(k1_ordinal1(sK0),sK1) | ~spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f47])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ( ! [X1] : (~r1_ordinal1(X1,sK1) | ~v3_ordinal1(X1) | ~r2_hidden(sK1,X1)) )),
% 0.22/0.50    inference(resolution,[],[f87,f40])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,sK1) | ~v3_ordinal1(X0) | ~r1_ordinal1(X0,sK1)) )),
% 0.22/0.50    inference(resolution,[],[f36,f27])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ~spl2_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    $false | ~spl2_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f27,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X1] : (~v3_ordinal1(X1)) ) | ~spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl2_3 <=> ! [X1] : ~v3_ordinal1(X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.50  % (11021)Refutation not found, incomplete strategy% (11021)------------------------------
% 0.22/0.50  % (11021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11021)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (11021)Memory used [KB]: 10618
% 0.22/0.50  % (11021)Time elapsed: 0.073 s
% 0.22/0.50  % (11021)------------------------------
% 0.22/0.50  % (11021)------------------------------
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl2_3 | spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f56,f53])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_ordinal1(X0,X0) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => r1_ordinal1(X0,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl2_1 | spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f47,f43])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ~spl2_1 | ~spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f47,f43])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (11037)------------------------------
% 0.22/0.50  % (11037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11037)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (11037)Memory used [KB]: 10746
% 0.22/0.50  % (11037)Time elapsed: 0.091 s
% 0.22/0.50  % (11037)------------------------------
% 0.22/0.50  % (11037)------------------------------
% 0.22/0.50  % (11014)Success in time 0.141 s
%------------------------------------------------------------------------------
