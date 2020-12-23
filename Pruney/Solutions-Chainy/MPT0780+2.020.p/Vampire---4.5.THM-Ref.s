%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:59 EST 2020

% Result     : Theorem 2.50s
% Output     : Refutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 178 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  208 ( 386 expanded)
%              Number of equality atoms :   42 (  98 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f129,f264,f298,f302,f377,f398])).

fof(f398,plain,
    ( spl3_12
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | spl3_12
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f31,f258,f255,f160])).

fof(f160,plain,(
    ! [X17] :
      ( r1_tarski(k1_relat_1(k2_wellord1(X17,sK0)),sK1)
      | ~ v1_relat_1(X17)
      | ~ v1_relat_1(k2_wellord1(X17,sK0)) ) ),
    inference(resolution,[],[f134,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f50,f32])).

fof(f32,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f134,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_relat_1(k2_wellord1(X2,X3)),X3)
      | ~ v1_relat_1(k2_wellord1(X2,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f132,f75])).

fof(f75,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X6,k3_relat_1(k2_wellord1(X7,X8)))
      | r1_tarski(X6,X8)
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f50,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

fof(f132,plain,(
    ! [X4] :
      ( r1_tarski(k1_relat_1(X4),k3_relat_1(X4))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f54,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f52])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f255,plain,
    ( ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl3_12
  <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f258,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl3_13
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f377,plain,
    ( ~ spl3_13
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | ~ spl3_13
    | spl3_20 ),
    inference(unit_resulting_resolution,[],[f31,f258,f297,f142])).

fof(f142,plain,(
    ! [X4] :
      ( r1_tarski(k2_relat_1(k2_wellord1(X4,sK0)),sK1)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k2_wellord1(X4,sK0)) ) ),
    inference(resolution,[],[f138,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_relat_1(k2_wellord1(X0,sK0)))
      | ~ v1_relat_1(X0)
      | r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f78,f50])).

fof(f78,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X0,sK0)),sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f72,f41])).

fof(f138,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f131,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k2_relat_1(X2))
      | r1_tarski(X3,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f55,f53])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f297,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl3_20
  <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f302,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f31,f259,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f259,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f257])).

fof(f298,plain,
    ( ~ spl3_13
    | ~ spl3_20
    | spl3_14 ),
    inference(avatar_split_clause,[],[f292,f261,f295,f257])).

fof(f261,plain,
    ( spl3_14
  <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f292,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_14 ),
    inference(trivial_inequality_removal,[],[f291])).

fof(f291,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
    | ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_14 ),
    inference(superposition,[],[f263,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f263,plain,
    ( k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f261])).

fof(f264,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | spl3_4 ),
    inference(avatar_split_clause,[],[f206,f123,f261,f257,f253])).

fof(f123,plain,
    ( spl3_4
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f206,plain,
    ( k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_4 ),
    inference(superposition,[],[f125,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k8_relat_1(X1,X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k8_relat_1(X1,X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

fof(f125,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f129,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f31,f121])).

fof(f121,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f127,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f110,f123,f119])).

fof(f110,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f33,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

fof(f33,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (791805952)
% 0.13/0.37  ipcrm: permission denied for id (791904261)
% 0.13/0.37  ipcrm: permission denied for id (791937030)
% 0.13/0.37  ipcrm: permission denied for id (792002568)
% 0.13/0.38  ipcrm: permission denied for id (792199184)
% 0.13/0.39  ipcrm: permission denied for id (792264722)
% 0.13/0.39  ipcrm: permission denied for id (792297491)
% 0.13/0.39  ipcrm: permission denied for id (792330260)
% 0.13/0.39  ipcrm: permission denied for id (792395798)
% 0.13/0.39  ipcrm: permission denied for id (792428568)
% 0.13/0.40  ipcrm: permission denied for id (792526876)
% 0.20/0.40  ipcrm: permission denied for id (792592415)
% 0.20/0.40  ipcrm: permission denied for id (792625184)
% 0.20/0.41  ipcrm: permission denied for id (792723491)
% 0.20/0.41  ipcrm: permission denied for id (792854567)
% 0.20/0.41  ipcrm: permission denied for id (792920104)
% 0.20/0.41  ipcrm: permission denied for id (792952873)
% 0.20/0.42  ipcrm: permission denied for id (793018411)
% 0.20/0.42  ipcrm: permission denied for id (793051180)
% 0.20/0.42  ipcrm: permission denied for id (793149487)
% 0.20/0.43  ipcrm: permission denied for id (793247796)
% 0.20/0.43  ipcrm: permission denied for id (793280566)
% 0.20/0.43  ipcrm: permission denied for id (793313335)
% 0.20/0.43  ipcrm: permission denied for id (793346105)
% 0.20/0.44  ipcrm: permission denied for id (793411643)
% 0.20/0.44  ipcrm: permission denied for id (793477181)
% 0.20/0.44  ipcrm: permission denied for id (793509950)
% 0.20/0.44  ipcrm: permission denied for id (793542719)
% 0.20/0.45  ipcrm: permission denied for id (793673798)
% 0.20/0.45  ipcrm: permission denied for id (793739337)
% 0.20/0.46  ipcrm: permission denied for id (793804875)
% 0.20/0.46  ipcrm: permission denied for id (793837644)
% 0.20/0.46  ipcrm: permission denied for id (793935952)
% 0.20/0.47  ipcrm: permission denied for id (794001490)
% 0.20/0.47  ipcrm: permission denied for id (794034259)
% 0.20/0.47  ipcrm: permission denied for id (794067028)
% 0.20/0.47  ipcrm: permission denied for id (794132567)
% 0.20/0.47  ipcrm: permission denied for id (794198105)
% 0.20/0.48  ipcrm: permission denied for id (794263644)
% 0.20/0.48  ipcrm: permission denied for id (794296413)
% 0.20/0.48  ipcrm: permission denied for id (794329182)
% 0.20/0.48  ipcrm: permission denied for id (794394720)
% 0.20/0.49  ipcrm: permission denied for id (794460260)
% 0.20/0.49  ipcrm: permission denied for id (794558567)
% 0.20/0.49  ipcrm: permission denied for id (794624104)
% 0.20/0.49  ipcrm: permission denied for id (794656873)
% 0.20/0.50  ipcrm: permission denied for id (794722411)
% 0.20/0.50  ipcrm: permission denied for id (794755180)
% 0.20/0.50  ipcrm: permission denied for id (794787950)
% 0.20/0.50  ipcrm: permission denied for id (794820720)
% 0.20/0.50  ipcrm: permission denied for id (794853489)
% 0.20/0.51  ipcrm: permission denied for id (794984565)
% 0.20/0.51  ipcrm: permission denied for id (795017334)
% 0.20/0.52  ipcrm: permission denied for id (795082874)
% 0.20/0.52  ipcrm: permission denied for id (795148412)
% 1.01/0.65  % (11730)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.01/0.65  % (11723)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.22/0.68  % (11736)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.22/0.70  % (11720)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.71  % (11712)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.71  % (11728)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.22/0.72  % (11708)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.22/0.72  % (11727)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.69/0.73  % (11711)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.69/0.73  % (11717)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.69/0.73  % (11715)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.69/0.73  % (11725)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.69/0.73  % (11719)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.69/0.73  % (11722)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.69/0.74  % (11731)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.69/0.74  % (11724)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.69/0.74  % (11716)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.69/0.74  % (11735)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.69/0.74  % (11714)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.69/0.75  % (11709)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.69/0.75  % (11713)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.69/0.75  % (11710)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.94/0.77  % (11737)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.94/0.77  % (11732)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.94/0.78  % (11729)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.94/0.78  % (11733)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.94/0.81  % (11721)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.94/0.82  % (11718)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.94/0.82  % (11726)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.50/0.84  % (11721)Refutation found. Thanks to Tanya!
% 2.50/0.84  % SZS status Theorem for theBenchmark
% 2.50/0.84  % SZS output start Proof for theBenchmark
% 2.50/0.84  fof(f399,plain,(
% 2.50/0.84    $false),
% 2.50/0.84    inference(avatar_sat_refutation,[],[f127,f129,f264,f298,f302,f377,f398])).
% 2.50/0.84  fof(f398,plain,(
% 2.50/0.84    spl3_12 | ~spl3_13),
% 2.50/0.84    inference(avatar_contradiction_clause,[],[f395])).
% 2.50/0.84  fof(f395,plain,(
% 2.50/0.84    $false | (spl3_12 | ~spl3_13)),
% 2.50/0.84    inference(unit_resulting_resolution,[],[f31,f258,f255,f160])).
% 2.50/0.84  fof(f160,plain,(
% 2.50/0.84    ( ! [X17] : (r1_tarski(k1_relat_1(k2_wellord1(X17,sK0)),sK1) | ~v1_relat_1(X17) | ~v1_relat_1(k2_wellord1(X17,sK0))) )),
% 2.50/0.84    inference(resolution,[],[f134,f72])).
% 2.50/0.84  fof(f72,plain,(
% 2.50/0.84    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK1)) )),
% 2.50/0.84    inference(resolution,[],[f50,f32])).
% 2.50/0.84  fof(f32,plain,(
% 2.50/0.84    r1_tarski(sK0,sK1)),
% 2.50/0.84    inference(cnf_transformation,[],[f18])).
% 2.50/0.84  fof(f18,plain,(
% 2.50/0.84    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 2.50/0.84    inference(flattening,[],[f17])).
% 2.50/0.84  fof(f17,plain,(
% 2.50/0.84    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 2.50/0.84    inference(ennf_transformation,[],[f16])).
% 2.50/0.84  fof(f16,negated_conjecture,(
% 2.50/0.84    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 2.50/0.84    inference(negated_conjecture,[],[f15])).
% 2.50/0.84  fof(f15,conjecture,(
% 2.50/0.84    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).
% 2.50/0.84  fof(f50,plain,(
% 2.50/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.50/0.84    inference(cnf_transformation,[],[f30])).
% 2.50/0.84  fof(f30,plain,(
% 2.50/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.50/0.84    inference(flattening,[],[f29])).
% 2.50/0.84  fof(f29,plain,(
% 2.50/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.50/0.84    inference(ennf_transformation,[],[f3])).
% 2.50/0.84  fof(f3,axiom,(
% 2.50/0.84    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.50/0.84  fof(f134,plain,(
% 2.50/0.84    ( ! [X2,X3] : (r1_tarski(k1_relat_1(k2_wellord1(X2,X3)),X3) | ~v1_relat_1(k2_wellord1(X2,X3)) | ~v1_relat_1(X2)) )),
% 2.50/0.84    inference(resolution,[],[f132,f75])).
% 2.50/0.84  fof(f75,plain,(
% 2.50/0.84    ( ! [X6,X8,X7] : (~r1_tarski(X6,k3_relat_1(k2_wellord1(X7,X8))) | r1_tarski(X6,X8) | ~v1_relat_1(X7)) )),
% 2.50/0.84    inference(resolution,[],[f50,f41])).
% 2.50/0.84  fof(f41,plain,(
% 2.50/0.84    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.50/0.84    inference(cnf_transformation,[],[f22])).
% 2.50/0.84  fof(f22,plain,(
% 2.50/0.84    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.50/0.84    inference(ennf_transformation,[],[f13])).
% 2.50/0.84  fof(f13,axiom,(
% 2.50/0.84    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).
% 2.50/0.84  fof(f132,plain,(
% 2.50/0.84    ( ! [X4] : (r1_tarski(k1_relat_1(X4),k3_relat_1(X4)) | ~v1_relat_1(X4)) )),
% 2.50/0.84    inference(superposition,[],[f54,f53])).
% 2.50/0.84  fof(f53,plain,(
% 2.50/0.84    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.50/0.84    inference(definition_unfolding,[],[f34,f52])).
% 2.50/0.84  fof(f52,plain,(
% 2.50/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.50/0.84    inference(definition_unfolding,[],[f36,f51])).
% 2.50/0.84  fof(f51,plain,(
% 2.50/0.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.50/0.84    inference(definition_unfolding,[],[f37,f47])).
% 2.50/0.84  fof(f47,plain,(
% 2.50/0.84    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.50/0.84    inference(cnf_transformation,[],[f6])).
% 2.50/0.84  fof(f6,axiom,(
% 2.50/0.84    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.50/0.84  fof(f37,plain,(
% 2.50/0.84    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.50/0.84    inference(cnf_transformation,[],[f5])).
% 2.50/0.84  fof(f5,axiom,(
% 2.50/0.84    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.50/0.84  fof(f36,plain,(
% 2.50/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.50/0.84    inference(cnf_transformation,[],[f7])).
% 2.50/0.84  fof(f7,axiom,(
% 2.50/0.84    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.50/0.84  fof(f34,plain,(
% 2.50/0.84    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 2.50/0.84    inference(cnf_transformation,[],[f19])).
% 2.50/0.84  fof(f19,plain,(
% 2.50/0.84    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.50/0.84    inference(ennf_transformation,[],[f8])).
% 2.50/0.84  fof(f8,axiom,(
% 2.50/0.84    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 2.50/0.84  fof(f54,plain,(
% 2.50/0.84    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.50/0.84    inference(definition_unfolding,[],[f35,f52])).
% 2.50/0.84  fof(f35,plain,(
% 2.50/0.84    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.50/0.84    inference(cnf_transformation,[],[f4])).
% 2.50/0.84  fof(f4,axiom,(
% 2.50/0.84    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.50/0.84  fof(f255,plain,(
% 2.50/0.84    ~r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_12),
% 2.50/0.84    inference(avatar_component_clause,[],[f253])).
% 2.50/0.84  fof(f253,plain,(
% 2.50/0.84    spl3_12 <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 2.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.50/0.84  fof(f258,plain,(
% 2.50/0.84    v1_relat_1(k2_wellord1(sK2,sK0)) | ~spl3_13),
% 2.50/0.84    inference(avatar_component_clause,[],[f257])).
% 2.50/0.84  fof(f257,plain,(
% 2.50/0.84    spl3_13 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 2.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.50/0.84  fof(f31,plain,(
% 2.50/0.84    v1_relat_1(sK2)),
% 2.50/0.84    inference(cnf_transformation,[],[f18])).
% 2.50/0.84  fof(f377,plain,(
% 2.50/0.84    ~spl3_13 | spl3_20),
% 2.50/0.84    inference(avatar_contradiction_clause,[],[f369])).
% 2.50/0.84  fof(f369,plain,(
% 2.50/0.84    $false | (~spl3_13 | spl3_20)),
% 2.50/0.84    inference(unit_resulting_resolution,[],[f31,f258,f297,f142])).
% 2.50/0.84  fof(f142,plain,(
% 2.50/0.84    ( ! [X4] : (r1_tarski(k2_relat_1(k2_wellord1(X4,sK0)),sK1) | ~v1_relat_1(X4) | ~v1_relat_1(k2_wellord1(X4,sK0))) )),
% 2.50/0.84    inference(resolution,[],[f138,f79])).
% 2.50/0.84  fof(f79,plain,(
% 2.50/0.84    ( ! [X0,X1] : (~r1_tarski(X1,k3_relat_1(k2_wellord1(X0,sK0))) | ~v1_relat_1(X0) | r1_tarski(X1,sK1)) )),
% 2.50/0.84    inference(resolution,[],[f78,f50])).
% 2.50/0.84  fof(f78,plain,(
% 2.50/0.84    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(X0,sK0)),sK1) | ~v1_relat_1(X0)) )),
% 2.50/0.84    inference(resolution,[],[f72,f41])).
% 2.50/0.84  fof(f138,plain,(
% 2.50/0.84    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.50/0.84    inference(resolution,[],[f131,f56])).
% 2.50/0.84  fof(f56,plain,(
% 2.50/0.84    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.50/0.84    inference(equality_resolution,[],[f45])).
% 2.50/0.84  fof(f45,plain,(
% 2.50/0.84    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.50/0.84    inference(cnf_transformation,[],[f1])).
% 2.50/0.84  fof(f1,axiom,(
% 2.50/0.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.50/0.84  fof(f131,plain,(
% 2.50/0.84    ( ! [X2,X3] : (~r1_tarski(X3,k2_relat_1(X2)) | r1_tarski(X3,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 2.50/0.84    inference(superposition,[],[f55,f53])).
% 2.50/0.84  fof(f55,plain,(
% 2.50/0.84    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.50/0.84    inference(definition_unfolding,[],[f49,f52])).
% 2.50/0.84  fof(f49,plain,(
% 2.50/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 2.50/0.84    inference(cnf_transformation,[],[f28])).
% 2.50/0.84  fof(f28,plain,(
% 2.50/0.84    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.50/0.84    inference(ennf_transformation,[],[f2])).
% 2.50/0.84  fof(f2,axiom,(
% 2.50/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.50/0.84  fof(f297,plain,(
% 2.50/0.84    ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_20),
% 2.50/0.84    inference(avatar_component_clause,[],[f295])).
% 2.50/0.84  fof(f295,plain,(
% 2.50/0.84    spl3_20 <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 2.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.50/0.84  fof(f302,plain,(
% 2.50/0.84    spl3_13),
% 2.50/0.84    inference(avatar_contradiction_clause,[],[f299])).
% 2.50/0.84  fof(f299,plain,(
% 2.50/0.84    $false | spl3_13),
% 2.50/0.84    inference(unit_resulting_resolution,[],[f31,f259,f38])).
% 2.50/0.84  fof(f38,plain,(
% 2.50/0.84    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.50/0.84    inference(cnf_transformation,[],[f20])).
% 2.50/0.84  fof(f20,plain,(
% 2.50/0.84    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 2.50/0.84    inference(ennf_transformation,[],[f11])).
% 2.50/0.84  fof(f11,axiom,(
% 2.50/0.84    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 2.50/0.84  fof(f259,plain,(
% 2.50/0.84    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_13),
% 2.50/0.84    inference(avatar_component_clause,[],[f257])).
% 2.50/0.84  fof(f298,plain,(
% 2.50/0.84    ~spl3_13 | ~spl3_20 | spl3_14),
% 2.50/0.84    inference(avatar_split_clause,[],[f292,f261,f295,f257])).
% 2.50/0.84  fof(f261,plain,(
% 2.50/0.84    spl3_14 <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))),
% 2.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.50/0.84  fof(f292,plain,(
% 2.50/0.84    ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_14),
% 2.50/0.84    inference(trivial_inequality_removal,[],[f291])).
% 2.50/0.84  fof(f291,plain,(
% 2.50/0.84    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) | ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_14),
% 2.50/0.84    inference(superposition,[],[f263,f42])).
% 2.50/0.84  fof(f42,plain,(
% 2.50/0.84    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.50/0.84    inference(cnf_transformation,[],[f24])).
% 2.50/0.84  fof(f24,plain,(
% 2.50/0.84    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.50/0.84    inference(flattening,[],[f23])).
% 2.50/0.84  fof(f23,plain,(
% 2.50/0.84    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.50/0.84    inference(ennf_transformation,[],[f9])).
% 2.50/0.84  fof(f9,axiom,(
% 2.50/0.84    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 2.50/0.84  fof(f263,plain,(
% 2.50/0.84    k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | spl3_14),
% 2.50/0.84    inference(avatar_component_clause,[],[f261])).
% 2.50/0.84  fof(f264,plain,(
% 2.50/0.84    ~spl3_12 | ~spl3_13 | ~spl3_14 | spl3_4),
% 2.50/0.84    inference(avatar_split_clause,[],[f206,f123,f261,f257,f253])).
% 2.50/0.84  fof(f123,plain,(
% 2.50/0.84    spl3_4 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 2.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.50/0.84  fof(f206,plain,(
% 2.50/0.84    k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_4),
% 2.50/0.84    inference(superposition,[],[f125,f84])).
% 2.50/0.84  fof(f84,plain,(
% 2.50/0.84    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k8_relat_1(X1,X0) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1)) )),
% 2.50/0.84    inference(duplicate_literal_removal,[],[f83])).
% 2.50/0.84  fof(f83,plain,(
% 2.50/0.84    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k8_relat_1(X1,X0) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 2.50/0.84    inference(superposition,[],[f39,f43])).
% 2.50/0.84  fof(f43,plain,(
% 2.50/0.84    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.50/0.84    inference(cnf_transformation,[],[f26])).
% 2.50/0.84  fof(f26,plain,(
% 2.50/0.84    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.50/0.84    inference(flattening,[],[f25])).
% 2.50/0.84  fof(f25,plain,(
% 2.50/0.84    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.50/0.84    inference(ennf_transformation,[],[f10])).
% 2.50/0.84  fof(f10,axiom,(
% 2.50/0.84    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 2.50/0.84  fof(f39,plain,(
% 2.50/0.84    ( ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.50/0.84    inference(cnf_transformation,[],[f21])).
% 2.50/0.84  fof(f21,plain,(
% 2.50/0.84    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.50/0.84    inference(ennf_transformation,[],[f12])).
% 2.50/0.84  fof(f12,axiom,(
% 2.50/0.84    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).
% 2.50/0.84  fof(f125,plain,(
% 2.50/0.84    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | spl3_4),
% 2.50/0.84    inference(avatar_component_clause,[],[f123])).
% 2.50/0.84  fof(f129,plain,(
% 2.50/0.84    spl3_3),
% 2.50/0.84    inference(avatar_contradiction_clause,[],[f128])).
% 2.50/0.84  fof(f128,plain,(
% 2.50/0.84    $false | spl3_3),
% 2.50/0.84    inference(subsumption_resolution,[],[f31,f121])).
% 2.50/0.84  fof(f121,plain,(
% 2.50/0.84    ~v1_relat_1(sK2) | spl3_3),
% 2.50/0.84    inference(avatar_component_clause,[],[f119])).
% 2.50/0.84  fof(f119,plain,(
% 2.50/0.84    spl3_3 <=> v1_relat_1(sK2)),
% 2.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.50/0.84  fof(f127,plain,(
% 2.50/0.84    ~spl3_3 | ~spl3_4),
% 2.50/0.84    inference(avatar_split_clause,[],[f110,f123,f119])).
% 2.50/0.84  fof(f110,plain,(
% 2.50/0.84    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(sK2)),
% 2.50/0.84    inference(superposition,[],[f33,f48])).
% 2.50/0.84  fof(f48,plain,(
% 2.50/0.84    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 2.50/0.84    inference(cnf_transformation,[],[f27])).
% 2.50/0.84  fof(f27,plain,(
% 2.50/0.84    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 2.50/0.84    inference(ennf_transformation,[],[f14])).
% 2.50/0.84  fof(f14,axiom,(
% 2.50/0.84    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 2.50/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).
% 2.50/0.84  fof(f33,plain,(
% 2.50/0.84    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 2.50/0.84    inference(cnf_transformation,[],[f18])).
% 2.50/0.84  % SZS output end Proof for theBenchmark
% 2.50/0.84  % (11721)------------------------------
% 2.50/0.84  % (11721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.50/0.84  % (11721)Termination reason: Refutation
% 2.50/0.84  
% 2.50/0.84  % (11721)Memory used [KB]: 6396
% 2.50/0.84  % (11721)Time elapsed: 0.252 s
% 2.50/0.84  % (11721)------------------------------
% 2.50/0.84  % (11721)------------------------------
% 2.50/0.85  % (11571)Success in time 0.485 s
%------------------------------------------------------------------------------
