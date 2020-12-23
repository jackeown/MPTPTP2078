%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0493+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  58 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   78 ( 122 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f25,f30,f36,f41,f47,f53])).

fof(f53,plain,
    ( ~ spl2_4
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | ~ spl2_4
    | spl2_6 ),
    inference(subsumption_resolution,[],[f49,f35])).

fof(f35,plain,
    ( sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_4
  <=> sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f49,plain,
    ( sK0 != k3_xboole_0(sK0,k1_relat_1(sK1))
    | spl2_6 ),
    inference(superposition,[],[f46,f13])).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f46,plain,
    ( sK0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_6
  <=> sK0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f47,plain,
    ( ~ spl2_6
    | spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f42,f39,f17,f44])).

fof(f17,plain,
    ( spl2_1
  <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f39,plain,
    ( spl2_5
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f42,plain,
    ( sK0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f19,f40])).

fof(f40,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f19,plain,
    ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f41,plain,
    ( spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f37,f27,f39])).

fof(f27,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f37,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_3 ),
    inference(resolution,[],[f14,f29])).

fof(f29,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f36,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f31,f22,f33])).

fof(f22,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f31,plain,
    ( sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f15,f24])).

fof(f24,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f30,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f10,f27])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f25,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f11,f22])).

fof(f11,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f20,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f12,f17])).

fof(f12,plain,(
    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
