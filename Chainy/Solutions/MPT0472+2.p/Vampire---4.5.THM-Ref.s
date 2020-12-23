%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0472+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  81 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 244 expanded)
%              Number of equality atoms :   33 ( 123 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1122,f1170,f1202,f1212,f1226])).

fof(f1226,plain,(
    ~ spl26_7 ),
    inference(avatar_contradiction_clause,[],[f1225])).

fof(f1225,plain,
    ( $false
    | ~ spl26_7 ),
    inference(subsumption_resolution,[],[f1220,f878])).

fof(f878,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f801])).

fof(f801,plain,
    ( k1_xboole_0 != sK0
    & ( k1_xboole_0 = k2_relat_1(sK0)
      | k1_xboole_0 = k1_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f710,f800])).

fof(f800,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != sK0
      & ( k1_xboole_0 = k2_relat_1(sK0)
        | k1_xboole_0 = k1_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f710,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f709])).

% (24869)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
fof(f709,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f707])).

fof(f707,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ( k1_xboole_0 = k2_relat_1(X0)
            | k1_xboole_0 = k1_relat_1(X0) )
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f706])).

fof(f706,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1220,plain,
    ( k1_xboole_0 = sK0
    | ~ spl26_7 ),
    inference(resolution,[],[f1165,f1030])).

fof(f1030,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f786])).

fof(f786,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1165,plain,
    ( v1_xboole_0(sK0)
    | ~ spl26_7 ),
    inference(avatar_component_clause,[],[f1163])).

fof(f1163,plain,
    ( spl26_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_7])])).

fof(f1212,plain,
    ( ~ spl26_1
    | spl26_8 ),
    inference(avatar_contradiction_clause,[],[f1211])).

fof(f1211,plain,
    ( $false
    | ~ spl26_1
    | spl26_8 ),
    inference(subsumption_resolution,[],[f1206,f1045])).

fof(f1045,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1206,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl26_1
    | spl26_8 ),
    inference(backward_demodulation,[],[f1169,f1117])).

fof(f1117,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl26_1 ),
    inference(avatar_component_clause,[],[f1115])).

fof(f1115,plain,
    ( spl26_1
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_1])])).

fof(f1169,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK0))
    | spl26_8 ),
    inference(avatar_component_clause,[],[f1167])).

fof(f1167,plain,
    ( spl26_8
  <=> v1_xboole_0(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_8])])).

fof(f1202,plain,(
    ~ spl26_2 ),
    inference(avatar_contradiction_clause,[],[f1201])).

fof(f1201,plain,
    ( $false
    | ~ spl26_2 ),
    inference(subsumption_resolution,[],[f1196,f878])).

fof(f1196,plain,
    ( k1_xboole_0 = sK0
    | ~ spl26_2 ),
    inference(resolution,[],[f1183,f1030])).

fof(f1183,plain,
    ( v1_xboole_0(sK0)
    | ~ spl26_2 ),
    inference(subsumption_resolution,[],[f1182,f876])).

fof(f876,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f801])).

fof(f1182,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl26_2 ),
    inference(subsumption_resolution,[],[f1172,f1045])).

fof(f1172,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl26_2 ),
    inference(superposition,[],[f891,f1121])).

fof(f1121,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl26_2 ),
    inference(avatar_component_clause,[],[f1119])).

fof(f1119,plain,
    ( spl26_2
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_2])])).

fof(f891,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f722])).

fof(f722,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f721])).

fof(f721,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f663])).

fof(f663,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f1170,plain,
    ( spl26_7
    | ~ spl26_8 ),
    inference(avatar_split_clause,[],[f1133,f1167,f1163])).

fof(f1133,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f876,f933])).

% (24852)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
fof(f933,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_xboole_0(k1_relat_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f743])).

fof(f743,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f742])).

fof(f742,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f662])).

fof(f662,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f1122,plain,
    ( spl26_1
    | spl26_2 ),
    inference(avatar_split_clause,[],[f877,f1119,f1115])).

fof(f877,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f801])).
%------------------------------------------------------------------------------
