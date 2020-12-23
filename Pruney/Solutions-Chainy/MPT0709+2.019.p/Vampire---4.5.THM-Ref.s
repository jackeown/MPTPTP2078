%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 145 expanded)
%              Number of leaves         :   18 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  263 ( 483 expanded)
%              Number of equality atoms :   35 (  68 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f65,f85,f94,f114,f122,f133,f142])).

fof(f142,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_5
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | spl2_5
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f44,f59,f64,f113,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ),
    inference(resolution,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f113,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl2_12
  <=> ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f64,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_5
  <=> sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f59,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_4
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f44,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f133,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_11 ),
    inference(subsumption_resolution,[],[f131,f44])).

fof(f131,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_2
    | spl2_11 ),
    inference(subsumption_resolution,[],[f129,f49])).

fof(f49,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f129,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_11 ),
    inference(resolution,[],[f110,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f110,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_11
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f122,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_10 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_10 ),
    inference(subsumption_resolution,[],[f120,f44])).

fof(f120,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_2
    | spl2_10 ),
    inference(subsumption_resolution,[],[f118,f49])).

fof(f118,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_10 ),
    inference(resolution,[],[f106,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f106,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl2_10
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f114,plain,
    ( ~ spl2_10
    | ~ spl2_11
    | spl2_12
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f97,f92,f83,f112,f108,f104])).

fof(f83,plain,
    ( spl2_8
  <=> ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f92,plain,
    ( spl2_9
  <=> ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f97,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
        | ~ v1_funct_1(k2_funct_1(sK1))
        | ~ v1_relat_1(k2_funct_1(sK1)) )
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f95,f84])).

fof(f84,plain,
    ( ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f95,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)),X0)
        | ~ v1_funct_1(k2_funct_1(sK1))
        | ~ v1_relat_1(k2_funct_1(sK1)) )
    | ~ spl2_9 ),
    inference(superposition,[],[f33,f93])).

fof(f93,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f94,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f88,f52,f47,f42,f92])).

fof(f52,plain,
    ( spl2_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f88,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f87,f44])).

fof(f87,plain,
    ( ! [X0] :
        ( k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f86,f49])).

fof(f86,plain,
    ( ! [X0] :
        ( k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3 ),
    inference(resolution,[],[f35,f54])).

fof(f54,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f85,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f81,f52,f47,f42,f83])).

fof(f81,plain,
    ( ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f80,f44])).

fof(f80,plain,
    ( ! [X0] :
        ( k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f79,f49])).

fof(f79,plain,
    ( ! [X0] :
        ( k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3 ),
    inference(resolution,[],[f34,f54])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f65,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f60,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:12:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (18496)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (18503)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (18511)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (18491)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (18501)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (18492)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (18509)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (18512)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (18493)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (18492)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (18495)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (18499)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (18500)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f65,f85,f94,f114,f122,f133,f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_4 | spl2_5 | ~spl2_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    $false | (~spl2_1 | ~spl2_4 | spl2_5 | ~spl2_12)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f44,f59,f64,f113,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0) )),
% 0.21/0.51    inference(resolution,[],[f32,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ) | ~spl2_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl2_12 <=> ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) | spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl2_5 <=> sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl2_4 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_2 | spl2_11),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    $false | (~spl2_1 | ~spl2_2 | spl2_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f131,f44])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | (~spl2_2 | spl2_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f129,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v1_funct_1(sK1) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    spl2_2 <=> v1_funct_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_11),
% 0.21/0.51    inference(resolution,[],[f110,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ~v1_funct_1(k2_funct_1(sK1)) | spl2_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl2_11 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_2 | spl2_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    $false | (~spl2_1 | ~spl2_2 | spl2_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f120,f44])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | (~spl2_2 | spl2_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f118,f49])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_10),
% 0.21/0.51    inference(resolution,[],[f106,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK1)) | spl2_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl2_10 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ~spl2_10 | ~spl2_11 | spl2_12 | ~spl2_8 | ~spl2_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f97,f92,f83,f112,f108,f104])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl2_8 <=> ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl2_9 <=> ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))) ) | (~spl2_8 | ~spl2_9)),
% 0.21/0.51    inference(forward_demodulation,[],[f95,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)) ) | ~spl2_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)),X0) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))) ) | ~spl2_9),
% 0.21/0.51    inference(superposition,[],[f33,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)) ) | ~spl2_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl2_9 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f88,f52,f47,f42,f92])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    spl2_3 <=> v2_funct_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f44])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f49])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl2_3),
% 0.21/0.51    inference(resolution,[],[f35,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    v2_funct_1(sK1) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f52])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl2_8 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f81,f52,f47,f42,f83])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f80,f44])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f79,f49])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl2_3),
% 0.21/0.51    inference(resolution,[],[f34,f54])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ~spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f62])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f27,f57])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f52])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    v2_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f26,f47])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f42])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (18492)------------------------------
% 0.21/0.52  % (18492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18492)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (18492)Memory used [KB]: 6140
% 0.21/0.52  % (18492)Time elapsed: 0.094 s
% 0.21/0.52  % (18492)------------------------------
% 0.21/0.52  % (18492)------------------------------
% 0.21/0.52  % (18508)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (18489)Success in time 0.155 s
%------------------------------------------------------------------------------
