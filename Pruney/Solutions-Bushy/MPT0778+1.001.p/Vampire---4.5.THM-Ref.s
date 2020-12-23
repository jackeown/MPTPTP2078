%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0778+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  47 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   69 ( 101 expanded)
%              Number of equality atoms :   23 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f22,f26,f30,f35,f39])).

fof(f39,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f38])).

fof(f38,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f37,f34])).

fof(f34,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f33])).

% (7972)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f33,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f37,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f36,f25])).

fof(f25,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_3
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f36,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK1,sK0))
    | spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f16,f34])).

fof(f16,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f14,plain,
    ( spl3_1
  <=> k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f31,f28,f19,f33])).

fof(f19,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f28,plain,
    ( spl3_4
  <=> ! [X1,X0,X2] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f31,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f29,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f28])).

fof(f30,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f12,f28])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(f26,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f11,f24])).

fof(f11,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f22,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f9,f19])).

fof(f9,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & v1_relat_1(X2) )
   => ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(f17,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f10,f14])).

fof(f10,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
