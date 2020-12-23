%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0022+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  51 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 (  90 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f275,f280,f308,f367])).

fof(f367,plain,
    ( ~ spl16_2
    | spl16_4 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl16_2
    | spl16_4 ),
    inference(subsumption_resolution,[],[f365,f298])).

fof(f298,plain,
    ( ~ v1_xboole_0(sK0)
    | spl16_4 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl16_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f365,plain,
    ( v1_xboole_0(sK0)
    | ~ spl16_2 ),
    inference(subsumption_resolution,[],[f335,f242])).

fof(f242,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f152,f153])).

fof(f153,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f152,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f335,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(sK0)
    | ~ spl16_2 ),
    inference(superposition,[],[f176,f279])).

fof(f279,plain,
    ( o_0_0_xboole_0 = k2_xboole_0(sK0,sK1)
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl16_2
  <=> o_0_0_xboole_0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).

fof(f308,plain,
    ( ~ spl16_4
    | spl16_1 ),
    inference(avatar_split_clause,[],[f283,f272,f296])).

fof(f272,plain,
    ( spl16_1
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f283,plain,
    ( ~ v1_xboole_0(sK0)
    | spl16_1 ),
    inference(unit_resulting_resolution,[],[f274,f246])).

fof(f246,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f157,f153])).

fof(f157,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

% (12806)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f274,plain,
    ( o_0_0_xboole_0 != sK0
    | spl16_1 ),
    inference(avatar_component_clause,[],[f272])).

fof(f280,plain,(
    spl16_2 ),
    inference(avatar_split_clause,[],[f241,f277])).

fof(f241,plain,(
    o_0_0_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(definition_unfolding,[],[f149,f153])).

fof(f149,plain,(
    k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,
    ( k1_xboole_0 != sK0
    & k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f66,f100])).

fof(f100,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != X0
        & k2_xboole_0(X0,X1) = k1_xboole_0 )
   => ( k1_xboole_0 != sK0
      & k1_xboole_0 = k2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & k2_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = k1_xboole_0
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f45])).

fof(f45,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f275,plain,(
    ~ spl16_1 ),
    inference(avatar_split_clause,[],[f240,f272])).

fof(f240,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f150,f153])).

fof(f150,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f101])).
%------------------------------------------------------------------------------
