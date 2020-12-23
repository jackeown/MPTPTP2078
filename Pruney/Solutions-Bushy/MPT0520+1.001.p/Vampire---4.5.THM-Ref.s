%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0520+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 189 expanded)
%              Number of equality atoms :   34 (  59 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f32,f36,f40,f44,f50,f55,f61,f67])).

fof(f67,plain,
    ( ~ spl2_4
    | ~ spl2_7
    | spl2_9 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_7
    | spl2_9 ),
    inference(subsumption_resolution,[],[f63,f49])).

fof(f49,plain,
    ( sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_7
  <=> sK0 = k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f63,plain,
    ( sK0 != k3_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_4
    | spl2_9 ),
    inference(superposition,[],[f60,f35])).

fof(f35,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f60,plain,
    ( sK0 != k3_xboole_0(k2_relat_1(sK1),sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_9
  <=> sK0 = k3_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f61,plain,
    ( ~ spl2_9
    | spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f56,f53,f19,f58])).

fof(f19,plain,
    ( spl2_1
  <=> sK0 = k2_relat_1(k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f53,plain,
    ( spl2_8
  <=> ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f56,plain,
    ( sK0 != k3_xboole_0(k2_relat_1(sK1),sK0)
    | spl2_1
    | ~ spl2_8 ),
    inference(superposition,[],[f21,f54])).

fof(f54,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f21,plain,
    ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f55,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f51,f38,f29,f53])).

fof(f29,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f38,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f51,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f50,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f45,f42,f24,f47])).

fof(f24,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f42,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f45,plain,
    ( sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f44,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f36,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f15,f34])).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f32,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f12,f29])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

fof(f27,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f13,f24])).

fof(f13,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f14,f19])).

fof(f14,plain,(
    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
