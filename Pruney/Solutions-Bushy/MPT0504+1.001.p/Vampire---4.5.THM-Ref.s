%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0504+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  51 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 111 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f28,f33,f39,f43])).

fof(f43,plain,
    ( ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f42])).

fof(f42,plain,
    ( $false
    | ~ spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f41,f22])).

fof(f22,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f41,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_5 ),
    inference(trivial_inequality_removal,[],[f40])).

fof(f40,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(sK2,sK0)
    | ~ r1_tarski(sK0,sK1)
    | spl3_5 ),
    inference(superposition,[],[f38,f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_5
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f39,plain,
    ( ~ spl3_5
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f34,f31,f15,f36])).

fof(f15,plain,
    ( spl3_1
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f31,plain,
    ( spl3_4
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f34,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f17,f32])).

fof(f32,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f17,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f33,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f29,f25,f31])).

fof(f25,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f29,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_3 ),
    inference(resolution,[],[f13,f27])).

fof(f27,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f28,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f9,f25])).

fof(f9,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(f23,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f10,f20])).

fof(f10,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f11,f15])).

fof(f11,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
