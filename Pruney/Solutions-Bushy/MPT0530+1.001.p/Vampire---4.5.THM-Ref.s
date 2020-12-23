%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0530+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  65 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   96 ( 164 expanded)
%              Number of equality atoms :   27 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f25,f30,f34,f38,f44,f49,f52])).

fof(f52,plain,
    ( spl3_1
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl3_1
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f50,f19])).

fof(f19,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl3_1
  <=> k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f48,f43])).

fof(f43,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_6
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f48,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_7
  <=> ! [X1,X0] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f49,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f45,f36,f27,f47])).

fof(f27,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f36,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f45,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f37,f29])).

fof(f29,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f37,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f36])).

fof(f44,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f39,f32,f22,f41])).

fof(f22,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f32,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f39,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f32])).

fof(f38,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f15,f36])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(f34,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f32])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    spl3_3 ),
    inference(avatar_split_clause,[],[f11,f27])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

fof(f25,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f22])).

fof(f12,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f13,f17])).

fof(f13,plain,(
    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
