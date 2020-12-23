%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:58 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 232 expanded)
%              Number of leaves         :   27 (  69 expanded)
%              Depth                    :   17
%              Number of atoms          :  251 ( 455 expanded)
%              Number of equality atoms :   54 ( 146 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f453,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f153,f155,f234,f271,f275,f448,f452])).

fof(f452,plain,
    ( spl3_12
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | spl3_12
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f40,f228,f225,f314])).

fof(f314,plain,(
    ! [X4] :
      ( v4_relat_1(k2_wellord1(X4,sK0),sK1)
      | ~ v1_relat_1(k2_wellord1(X4,sK0))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f289,f102])).

fof(f102,plain,(
    ! [X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,sK0)),sK1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f99,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

fof(f99,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,sK0)
      | r1_tarski(X11,sK1) ) ),
    inference(resolution,[],[f62,f41])).

fof(f41,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k3_relat_1(X0),X1)
      | v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f287,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | v4_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f287,plain,(
    ! [X5] :
      ( v4_relat_1(X5,k3_relat_1(X5))
      | ~ v1_relat_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X5)
      | v4_relat_1(X5,k3_relat_1(X5)) ) ),
    inference(resolution,[],[f279,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f279,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(X2),k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f74,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f44,f72])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f225,plain,
    ( ~ v4_relat_1(k2_wellord1(sK2,sK0),sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl3_12
  <=> v4_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f228,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl3_13
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f448,plain,
    ( ~ spl3_13
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl3_13
    | spl3_20 ),
    inference(unit_resulting_resolution,[],[f40,f228,f270,f309])).

fof(f309,plain,(
    ! [X4] :
      ( r1_tarski(k2_relat_1(k2_wellord1(X4,sK0)),sK1)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k2_wellord1(X4,sK0)) ) ),
    inference(resolution,[],[f304,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_relat_1(k2_wellord1(X0,sK0)))
      | ~ v1_relat_1(X0)
      | r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f102,f62])).

fof(f304,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f278,f76])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
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

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X0))
      | r1_tarski(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f75,f73])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f270,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl3_20
  <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f275,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f40,f229,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f229,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f227])).

fof(f271,plain,
    ( ~ spl3_13
    | ~ spl3_20
    | spl3_14 ),
    inference(avatar_split_clause,[],[f265,f231,f268,f227])).

fof(f231,plain,
    ( spl3_14
  <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f265,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_14 ),
    inference(trivial_inequality_removal,[],[f264])).

fof(f264,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
    | ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_14 ),
    inference(superposition,[],[f233,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f233,plain,
    ( k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f231])).

fof(f234,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | spl3_4 ),
    inference(avatar_split_clause,[],[f181,f149,f231,f227,f223])).

fof(f149,plain,
    ( spl3_4
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f181,plain,
    ( k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ v4_relat_1(k2_wellord1(sK2,sK0),sK1)
    | spl3_4 ),
    inference(superposition,[],[f151,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k8_relat_1(X1,X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k8_relat_1(X1,X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f48,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

fof(f151,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f149])).

fof(f155,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f40,f147])).

fof(f147,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f153,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f137,f149,f145])).

fof(f137,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f42,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

fof(f42,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:59:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (17229)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (17231)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (17221)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (17214)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (17223)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (17216)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (17207)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.31/0.53  % (17228)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.53  % (17220)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.31/0.53  % (17208)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.31/0.53  % (17209)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.31/0.54  % (17234)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.31/0.54  % (17212)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (17211)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.54  % (17206)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.54  % (17233)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.54  % (17230)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.54  % (17210)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.31/0.54  % (17235)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.54  % (17232)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.55  % (17222)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.31/0.55  % (17227)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.55  % (17224)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.31/0.55  % (17226)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.55  % (17218)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.31/0.55  % (17215)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.55  % (17219)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.56  % (17217)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.50/0.56  % (17225)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.50/0.56  % (17213)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.58  % (17219)Refutation found. Thanks to Tanya!
% 1.50/0.58  % SZS status Theorem for theBenchmark
% 1.50/0.58  % SZS output start Proof for theBenchmark
% 1.50/0.58  fof(f453,plain,(
% 1.50/0.58    $false),
% 1.50/0.58    inference(avatar_sat_refutation,[],[f153,f155,f234,f271,f275,f448,f452])).
% 1.50/0.58  fof(f452,plain,(
% 1.50/0.58    spl3_12 | ~spl3_13),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f449])).
% 1.50/0.58  fof(f449,plain,(
% 1.50/0.58    $false | (spl3_12 | ~spl3_13)),
% 1.50/0.58    inference(unit_resulting_resolution,[],[f40,f228,f225,f314])).
% 1.50/0.58  fof(f314,plain,(
% 1.50/0.58    ( ! [X4] : (v4_relat_1(k2_wellord1(X4,sK0),sK1) | ~v1_relat_1(k2_wellord1(X4,sK0)) | ~v1_relat_1(X4)) )),
% 1.50/0.58    inference(resolution,[],[f289,f102])).
% 1.50/0.58  fof(f102,plain,(
% 1.50/0.58    ( ! [X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,sK0)),sK1) | ~v1_relat_1(X1)) )),
% 1.50/0.58    inference(resolution,[],[f99,f50])).
% 1.50/0.58  fof(f50,plain,(
% 1.50/0.58    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f28])).
% 1.50/0.58  fof(f28,plain,(
% 1.50/0.58    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(ennf_transformation,[],[f19])).
% 1.50/0.58  fof(f19,axiom,(
% 1.50/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).
% 1.50/0.58  fof(f99,plain,(
% 1.50/0.58    ( ! [X11] : (~r1_tarski(X11,sK0) | r1_tarski(X11,sK1)) )),
% 1.50/0.58    inference(resolution,[],[f62,f41])).
% 1.50/0.58  fof(f41,plain,(
% 1.50/0.58    r1_tarski(sK0,sK1)),
% 1.50/0.58    inference(cnf_transformation,[],[f24])).
% 1.50/0.58  fof(f24,plain,(
% 1.50/0.58    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.50/0.58    inference(flattening,[],[f23])).
% 1.50/0.58  fof(f23,plain,(
% 1.50/0.58    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.50/0.58    inference(ennf_transformation,[],[f22])).
% 1.50/0.58  fof(f22,negated_conjecture,(
% 1.50/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.50/0.58    inference(negated_conjecture,[],[f21])).
% 1.50/0.58  fof(f21,conjecture,(
% 1.50/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).
% 1.50/0.58  fof(f62,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f39])).
% 1.50/0.58  fof(f39,plain,(
% 1.50/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.50/0.58    inference(flattening,[],[f38])).
% 1.50/0.58  fof(f38,plain,(
% 1.50/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.50/0.58    inference(ennf_transformation,[],[f3])).
% 1.50/0.58  fof(f3,axiom,(
% 1.50/0.58    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.50/0.58  fof(f289,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~r1_tarski(k3_relat_1(X0),X1) | ~v1_relat_1(X0) | v4_relat_1(X0,X1)) )),
% 1.50/0.58    inference(duplicate_literal_removal,[],[f288])).
% 1.50/0.58  fof(f288,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(k3_relat_1(X0),X1) | v4_relat_1(X0,X1)) )),
% 1.50/0.58    inference(resolution,[],[f287,f54])).
% 1.50/0.58  fof(f54,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1) | v4_relat_1(X2,X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f33])).
% 1.50/0.58  fof(f33,plain,(
% 1.50/0.58    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 1.50/0.58    inference(flattening,[],[f32])).
% 1.50/0.58  fof(f32,plain,(
% 1.50/0.58    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 1.50/0.58    inference(ennf_transformation,[],[f16])).
% 1.50/0.58  fof(f16,axiom,(
% 1.50/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 1.50/0.58  fof(f287,plain,(
% 1.50/0.58    ( ! [X5] : (v4_relat_1(X5,k3_relat_1(X5)) | ~v1_relat_1(X5)) )),
% 1.50/0.58    inference(duplicate_literal_removal,[],[f284])).
% 1.50/0.58  fof(f284,plain,(
% 1.50/0.58    ( ! [X5] : (~v1_relat_1(X5) | ~v1_relat_1(X5) | v4_relat_1(X5,k3_relat_1(X5))) )),
% 1.50/0.58    inference(resolution,[],[f279,f52])).
% 1.50/0.58  fof(f52,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | v4_relat_1(X1,X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f31])).
% 1.50/0.58  fof(f31,plain,(
% 1.50/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(ennf_transformation,[],[f12])).
% 1.50/0.58  fof(f12,axiom,(
% 1.50/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.50/0.58  fof(f279,plain,(
% 1.50/0.58    ( ! [X2] : (r1_tarski(k1_relat_1(X2),k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.50/0.58    inference(superposition,[],[f74,f73])).
% 1.50/0.58  fof(f73,plain,(
% 1.50/0.58    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f43,f72])).
% 1.50/0.58  fof(f72,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.50/0.58    inference(definition_unfolding,[],[f45,f71])).
% 1.50/0.58  fof(f71,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f46,f70])).
% 1.50/0.58  fof(f70,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f59,f69])).
% 1.50/0.58  fof(f69,plain,(
% 1.50/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f63,f68])).
% 1.50/0.58  fof(f68,plain,(
% 1.50/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f64,f67])).
% 1.50/0.58  fof(f67,plain,(
% 1.50/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f65,f66])).
% 1.50/0.58  fof(f66,plain,(
% 1.50/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f10])).
% 1.50/0.58  fof(f10,axiom,(
% 1.50/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.50/0.58  fof(f65,plain,(
% 1.50/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f9])).
% 1.50/0.58  fof(f9,axiom,(
% 1.50/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.50/0.58  fof(f64,plain,(
% 1.50/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f8])).
% 1.50/0.58  fof(f8,axiom,(
% 1.50/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.50/0.58  fof(f63,plain,(
% 1.50/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f7])).
% 1.50/0.58  fof(f7,axiom,(
% 1.50/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.50/0.58  fof(f59,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f6])).
% 1.50/0.58  fof(f6,axiom,(
% 1.50/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.58  fof(f46,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f5])).
% 1.50/0.58  fof(f5,axiom,(
% 1.50/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.58  fof(f45,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f11])).
% 1.50/0.58  fof(f11,axiom,(
% 1.50/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.50/0.58  fof(f43,plain,(
% 1.50/0.58    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f25])).
% 1.50/0.58  fof(f25,plain,(
% 1.50/0.58    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.50/0.58    inference(ennf_transformation,[],[f13])).
% 1.50/0.58  fof(f13,axiom,(
% 1.50/0.58    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 1.50/0.58  fof(f74,plain,(
% 1.50/0.58    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.50/0.58    inference(definition_unfolding,[],[f44,f72])).
% 1.50/0.58  fof(f44,plain,(
% 1.50/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f4])).
% 1.50/0.58  fof(f4,axiom,(
% 1.50/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.50/0.58  fof(f225,plain,(
% 1.50/0.58    ~v4_relat_1(k2_wellord1(sK2,sK0),sK1) | spl3_12),
% 1.50/0.58    inference(avatar_component_clause,[],[f223])).
% 1.50/0.58  fof(f223,plain,(
% 1.50/0.58    spl3_12 <=> v4_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.50/0.58  fof(f228,plain,(
% 1.50/0.58    v1_relat_1(k2_wellord1(sK2,sK0)) | ~spl3_13),
% 1.50/0.58    inference(avatar_component_clause,[],[f227])).
% 1.50/0.58  fof(f227,plain,(
% 1.50/0.58    spl3_13 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.50/0.58  fof(f40,plain,(
% 1.50/0.58    v1_relat_1(sK2)),
% 1.50/0.58    inference(cnf_transformation,[],[f24])).
% 1.50/0.58  fof(f448,plain,(
% 1.50/0.58    ~spl3_13 | spl3_20),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f440])).
% 1.50/0.58  fof(f440,plain,(
% 1.50/0.58    $false | (~spl3_13 | spl3_20)),
% 1.50/0.58    inference(unit_resulting_resolution,[],[f40,f228,f270,f309])).
% 1.50/0.58  fof(f309,plain,(
% 1.50/0.58    ( ! [X4] : (r1_tarski(k2_relat_1(k2_wellord1(X4,sK0)),sK1) | ~v1_relat_1(X4) | ~v1_relat_1(k2_wellord1(X4,sK0))) )),
% 1.50/0.58    inference(resolution,[],[f304,f103])).
% 1.50/0.58  fof(f103,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~r1_tarski(X1,k3_relat_1(k2_wellord1(X0,sK0))) | ~v1_relat_1(X0) | r1_tarski(X1,sK1)) )),
% 1.50/0.58    inference(resolution,[],[f102,f62])).
% 1.50/0.58  fof(f304,plain,(
% 1.50/0.58    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(resolution,[],[f278,f76])).
% 1.50/0.58  fof(f76,plain,(
% 1.50/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.58    inference(equality_resolution,[],[f57])).
% 1.50/0.58  fof(f57,plain,(
% 1.50/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.50/0.58    inference(cnf_transformation,[],[f1])).
% 1.50/0.58  fof(f1,axiom,(
% 1.50/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.58  fof(f278,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~r1_tarski(X1,k2_relat_1(X0)) | r1_tarski(X1,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(superposition,[],[f75,f73])).
% 1.50/0.58  fof(f75,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f61,f72])).
% 1.50/0.58  fof(f61,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f37])).
% 1.50/0.58  fof(f37,plain,(
% 1.50/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.50/0.58    inference(ennf_transformation,[],[f2])).
% 1.50/0.58  fof(f2,axiom,(
% 1.50/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.50/0.58  fof(f270,plain,(
% 1.50/0.58    ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_20),
% 1.50/0.58    inference(avatar_component_clause,[],[f268])).
% 1.50/0.58  fof(f268,plain,(
% 1.50/0.58    spl3_20 <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.50/0.58  fof(f275,plain,(
% 1.50/0.58    spl3_13),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f272])).
% 1.50/0.58  fof(f272,plain,(
% 1.50/0.58    $false | spl3_13),
% 1.50/0.58    inference(unit_resulting_resolution,[],[f40,f229,f47])).
% 1.50/0.58  fof(f47,plain,(
% 1.50/0.58    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f26])).
% 1.50/0.58  fof(f26,plain,(
% 1.50/0.58    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.50/0.58    inference(ennf_transformation,[],[f17])).
% 1.50/0.58  fof(f17,axiom,(
% 1.50/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.50/0.58  fof(f229,plain,(
% 1.50/0.58    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_13),
% 1.50/0.58    inference(avatar_component_clause,[],[f227])).
% 1.50/0.58  fof(f271,plain,(
% 1.50/0.58    ~spl3_13 | ~spl3_20 | spl3_14),
% 1.50/0.58    inference(avatar_split_clause,[],[f265,f231,f268,f227])).
% 1.50/0.58  fof(f231,plain,(
% 1.50/0.58    spl3_14 <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.50/0.58  fof(f265,plain,(
% 1.50/0.58    ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_14),
% 1.50/0.58    inference(trivial_inequality_removal,[],[f264])).
% 1.50/0.58  fof(f264,plain,(
% 1.50/0.58    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) | ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_14),
% 1.50/0.58    inference(superposition,[],[f233,f51])).
% 1.50/0.58  fof(f51,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f30])).
% 1.50/0.58  fof(f30,plain,(
% 1.50/0.58    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(flattening,[],[f29])).
% 1.50/0.58  fof(f29,plain,(
% 1.50/0.58    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(ennf_transformation,[],[f14])).
% 1.50/0.58  fof(f14,axiom,(
% 1.50/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.50/0.58  fof(f233,plain,(
% 1.50/0.58    k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | spl3_14),
% 1.50/0.58    inference(avatar_component_clause,[],[f231])).
% 1.50/0.58  fof(f234,plain,(
% 1.50/0.58    ~spl3_12 | ~spl3_13 | ~spl3_14 | spl3_4),
% 1.50/0.58    inference(avatar_split_clause,[],[f181,f149,f231,f227,f223])).
% 1.50/0.58  fof(f149,plain,(
% 1.50/0.58    spl3_4 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.50/0.58  fof(f181,plain,(
% 1.50/0.58    k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~v4_relat_1(k2_wellord1(sK2,sK0),sK1) | spl3_4),
% 1.50/0.58    inference(superposition,[],[f151,f110])).
% 1.50/0.58  fof(f110,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k8_relat_1(X1,X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 1.50/0.58    inference(duplicate_literal_removal,[],[f109])).
% 1.50/0.58  fof(f109,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k8_relat_1(X1,X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(superposition,[],[f48,f55])).
% 1.50/0.58  fof(f55,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f35])).
% 1.50/0.58  fof(f35,plain,(
% 1.50/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(flattening,[],[f34])).
% 1.50/0.58  fof(f34,plain,(
% 1.50/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.50/0.58    inference(ennf_transformation,[],[f15])).
% 1.50/0.58  fof(f15,axiom,(
% 1.50/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.50/0.58  fof(f48,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f27])).
% 1.50/0.58  fof(f27,plain,(
% 1.50/0.58    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(ennf_transformation,[],[f18])).
% 1.50/0.58  fof(f18,axiom,(
% 1.50/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).
% 1.50/0.58  fof(f151,plain,(
% 1.50/0.58    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | spl3_4),
% 1.50/0.58    inference(avatar_component_clause,[],[f149])).
% 1.50/0.58  fof(f155,plain,(
% 1.50/0.58    spl3_3),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f154])).
% 1.50/0.58  fof(f154,plain,(
% 1.50/0.58    $false | spl3_3),
% 1.50/0.58    inference(subsumption_resolution,[],[f40,f147])).
% 1.50/0.58  fof(f147,plain,(
% 1.50/0.58    ~v1_relat_1(sK2) | spl3_3),
% 1.50/0.58    inference(avatar_component_clause,[],[f145])).
% 1.50/0.58  fof(f145,plain,(
% 1.50/0.58    spl3_3 <=> v1_relat_1(sK2)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.50/0.58  fof(f153,plain,(
% 1.50/0.58    ~spl3_3 | ~spl3_4),
% 1.50/0.58    inference(avatar_split_clause,[],[f137,f149,f145])).
% 1.50/0.58  fof(f137,plain,(
% 1.50/0.58    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(sK2)),
% 1.50/0.58    inference(superposition,[],[f42,f60])).
% 1.50/0.58  fof(f60,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f36])).
% 1.50/0.58  fof(f36,plain,(
% 1.50/0.58    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 1.50/0.58    inference(ennf_transformation,[],[f20])).
% 1.50/0.58  fof(f20,axiom,(
% 1.50/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).
% 1.50/0.58  fof(f42,plain,(
% 1.50/0.58    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 1.50/0.58    inference(cnf_transformation,[],[f24])).
% 1.50/0.58  % SZS output end Proof for theBenchmark
% 1.50/0.58  % (17219)------------------------------
% 1.50/0.58  % (17219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (17219)Termination reason: Refutation
% 1.50/0.58  
% 1.50/0.58  % (17219)Memory used [KB]: 6396
% 1.50/0.58  % (17219)Time elapsed: 0.157 s
% 1.50/0.58  % (17219)------------------------------
% 1.50/0.58  % (17219)------------------------------
% 1.50/0.58  % (17205)Success in time 0.225 s
%------------------------------------------------------------------------------
