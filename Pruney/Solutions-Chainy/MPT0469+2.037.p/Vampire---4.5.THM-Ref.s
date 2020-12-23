%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:39 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 239 expanded)
%              Number of leaves         :   28 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 ( 425 expanded)
%              Number of equality atoms :   61 ( 174 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f111,f117,f120,f130])).

fof(f130,plain,
    ( spl9_2
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f128,f85])).

fof(f85,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl9_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f128,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl9_4 ),
    inference(resolution,[],[f125,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f125,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl9_4 ),
    inference(resolution,[],[f106,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f106,plain,
    ( ! [X4] : ~ r2_hidden(X4,k2_relat_1(k1_xboole_0))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl9_4
  <=> ! [X4] : ~ r2_hidden(X4,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f120,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl9_3 ),
    inference(subsumption_resolution,[],[f118,f89])).

fof(f89,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f88,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f65,f66])).

% (20591)Termination reason: Refutation not found, incomplete strategy

% (20591)Memory used [KB]: 10618
fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

% (20591)Time elapsed: 0.111 s
% (20591)------------------------------
% (20591)------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f88,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))) ),
    inference(resolution,[],[f74,f45])).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

% (20580)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f56,f72])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f118,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | spl9_3 ),
    inference(resolution,[],[f103,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f32,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f103,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl9_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f117,plain,
    ( ~ spl9_3
    | spl9_4
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f116,f79,f105,f101])).

fof(f79,plain,
    ( spl9_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f114,f89])).

fof(f114,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl9_1 ),
    inference(superposition,[],[f57,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f36])).

fof(f36,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK5(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f111,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f109,f81])).

fof(f81,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f109,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f97,f47])).

fof(f97,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f90,f49])).

fof(f90,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f89,f77])).

fof(f77,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f86,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f44,f83,f79])).

fof(f44,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:54:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (20591)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.26/0.53  % (20577)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.53  % (20577)Refutation found. Thanks to Tanya!
% 1.26/0.53  % SZS status Theorem for theBenchmark
% 1.26/0.53  % (20591)Refutation not found, incomplete strategy% (20591)------------------------------
% 1.26/0.53  % (20591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % SZS output start Proof for theBenchmark
% 1.26/0.53  fof(f131,plain,(
% 1.26/0.53    $false),
% 1.26/0.53    inference(avatar_sat_refutation,[],[f86,f111,f117,f120,f130])).
% 1.26/0.53  fof(f130,plain,(
% 1.26/0.53    spl9_2 | ~spl9_4),
% 1.26/0.53    inference(avatar_contradiction_clause,[],[f129])).
% 1.26/0.53  fof(f129,plain,(
% 1.26/0.53    $false | (spl9_2 | ~spl9_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f128,f85])).
% 1.26/0.53  fof(f85,plain,(
% 1.26/0.53    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl9_2),
% 1.26/0.53    inference(avatar_component_clause,[],[f83])).
% 1.26/0.53  fof(f83,plain,(
% 1.26/0.53    spl9_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.26/0.53  fof(f128,plain,(
% 1.26/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl9_4),
% 1.26/0.53    inference(resolution,[],[f125,f47])).
% 1.26/0.53  fof(f47,plain,(
% 1.26/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.26/0.53    inference(cnf_transformation,[],[f20])).
% 1.26/0.53  fof(f20,plain,(
% 1.26/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f2])).
% 1.26/0.53  fof(f2,axiom,(
% 1.26/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.26/0.53  fof(f125,plain,(
% 1.26/0.53    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl9_4),
% 1.26/0.53    inference(resolution,[],[f106,f49])).
% 1.26/0.53  fof(f49,plain,(
% 1.26/0.53    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_xboole_0(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f28])).
% 1.26/0.53  fof(f28,plain,(
% 1.26/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.26/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 1.26/0.53  fof(f27,plain,(
% 1.26/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f26,plain,(
% 1.26/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.26/0.53    inference(rectify,[],[f25])).
% 1.26/0.53  fof(f25,plain,(
% 1.26/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.26/0.53    inference(nnf_transformation,[],[f1])).
% 1.26/0.53  fof(f1,axiom,(
% 1.26/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.26/0.53  fof(f106,plain,(
% 1.26/0.53    ( ! [X4] : (~r2_hidden(X4,k2_relat_1(k1_xboole_0))) ) | ~spl9_4),
% 1.26/0.53    inference(avatar_component_clause,[],[f105])).
% 1.26/0.53  fof(f105,plain,(
% 1.26/0.53    spl9_4 <=> ! [X4] : ~r2_hidden(X4,k2_relat_1(k1_xboole_0))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.26/0.53  fof(f120,plain,(
% 1.26/0.53    spl9_3),
% 1.26/0.53    inference(avatar_contradiction_clause,[],[f119])).
% 1.26/0.53  fof(f119,plain,(
% 1.26/0.53    $false | spl9_3),
% 1.26/0.53    inference(subsumption_resolution,[],[f118,f89])).
% 1.26/0.53  fof(f89,plain,(
% 1.26/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.26/0.53    inference(forward_demodulation,[],[f88,f73])).
% 1.26/0.53  fof(f73,plain,(
% 1.26/0.53    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.26/0.53    inference(definition_unfolding,[],[f46,f72])).
% 1.26/0.53  fof(f72,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.26/0.53    inference(definition_unfolding,[],[f53,f71])).
% 1.26/0.53  fof(f71,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.26/0.53    inference(definition_unfolding,[],[f54,f70])).
% 1.26/0.53  fof(f70,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.26/0.53    inference(definition_unfolding,[],[f62,f69])).
% 1.26/0.53  fof(f69,plain,(
% 1.26/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.26/0.53    inference(definition_unfolding,[],[f63,f68])).
% 1.26/0.53  fof(f68,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.26/0.53    inference(definition_unfolding,[],[f64,f67])).
% 1.26/0.53  fof(f67,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.26/0.53    inference(definition_unfolding,[],[f65,f66])).
% 1.26/0.53  % (20591)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (20591)Memory used [KB]: 10618
% 1.26/0.53  fof(f66,plain,(
% 1.26/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f11])).
% 1.26/0.53  % (20591)Time elapsed: 0.111 s
% 1.26/0.53  % (20591)------------------------------
% 1.26/0.53  % (20591)------------------------------
% 1.26/0.53  fof(f11,axiom,(
% 1.26/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.26/0.53  fof(f65,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f10])).
% 1.26/0.53  fof(f10,axiom,(
% 1.26/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.26/0.53  fof(f64,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f9])).
% 1.26/0.53  fof(f9,axiom,(
% 1.26/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.26/0.53  fof(f63,plain,(
% 1.26/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f8,axiom,(
% 1.26/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.26/0.53  fof(f62,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f7])).
% 1.26/0.53  fof(f7,axiom,(
% 1.26/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.26/0.53  fof(f54,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f6])).
% 1.26/0.53  fof(f6,axiom,(
% 1.26/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.26/0.53  fof(f53,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.26/0.53    inference(cnf_transformation,[],[f12])).
% 1.26/0.53  fof(f12,axiom,(
% 1.26/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.26/0.53  fof(f46,plain,(
% 1.26/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f4])).
% 1.26/0.53  fof(f4,axiom,(
% 1.26/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.26/0.53  fof(f88,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)))) )),
% 1.26/0.53    inference(resolution,[],[f74,f45])).
% 1.26/0.53  fof(f45,plain,(
% 1.26/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f5])).
% 1.26/0.53  fof(f5,axiom,(
% 1.26/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.26/0.53  % (20580)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.53  fof(f74,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.26/0.53    inference(definition_unfolding,[],[f56,f72])).
% 1.26/0.53  fof(f56,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.26/0.53    inference(cnf_transformation,[],[f35])).
% 1.26/0.53  fof(f35,plain,(
% 1.26/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.26/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f34])).
% 1.26/0.53  fof(f34,plain,(
% 1.26/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f22,plain,(
% 1.26/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.26/0.53    inference(ennf_transformation,[],[f18])).
% 1.26/0.53  fof(f18,plain,(
% 1.26/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.26/0.53    inference(rectify,[],[f3])).
% 1.26/0.53  fof(f3,axiom,(
% 1.26/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.26/0.53  fof(f118,plain,(
% 1.26/0.53    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | spl9_3),
% 1.26/0.53    inference(resolution,[],[f103,f51])).
% 1.26/0.53  fof(f51,plain,(
% 1.26/0.53    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f33])).
% 1.26/0.53  fof(f33,plain,(
% 1.26/0.53    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.26/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f32,f31])).
% 1.26/0.53  fof(f31,plain,(
% 1.26/0.53    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f32,plain,(
% 1.26/0.53    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f30,plain,(
% 1.26/0.53    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.26/0.53    inference(rectify,[],[f29])).
% 1.26/0.53  fof(f29,plain,(
% 1.26/0.53    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.26/0.53    inference(nnf_transformation,[],[f21])).
% 1.26/0.53  fof(f21,plain,(
% 1.26/0.53    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f13])).
% 1.26/0.53  fof(f13,axiom,(
% 1.26/0.53    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.26/0.53  fof(f103,plain,(
% 1.26/0.53    ~v1_relat_1(k1_xboole_0) | spl9_3),
% 1.26/0.53    inference(avatar_component_clause,[],[f101])).
% 1.26/0.54  fof(f101,plain,(
% 1.26/0.54    spl9_3 <=> v1_relat_1(k1_xboole_0)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.26/0.54  fof(f117,plain,(
% 1.26/0.54    ~spl9_3 | spl9_4 | ~spl9_1),
% 1.26/0.54    inference(avatar_split_clause,[],[f116,f79,f105,f101])).
% 1.26/0.54  fof(f79,plain,(
% 1.26/0.54    spl9_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.26/0.54  fof(f116,plain,(
% 1.26/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl9_1),
% 1.26/0.54    inference(subsumption_resolution,[],[f114,f89])).
% 1.26/0.54  fof(f114,plain,(
% 1.26/0.54    ( ! [X0] : (r2_hidden(sK5(k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl9_1),
% 1.26/0.54    inference(superposition,[],[f57,f80])).
% 1.26/0.54  fof(f80,plain,(
% 1.26/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl9_1),
% 1.26/0.54    inference(avatar_component_clause,[],[f79])).
% 1.26/0.54  fof(f57,plain,(
% 1.26/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f37])).
% 1.26/0.54  fof(f37,plain,(
% 1.26/0.54    ! [X0,X1] : (r2_hidden(sK5(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f36])).
% 1.26/0.54  fof(f36,plain,(
% 1.26/0.54    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK5(X1),k1_relat_1(X1)))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f24,plain,(
% 1.26/0.54    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.26/0.54    inference(flattening,[],[f23])).
% 1.26/0.54  fof(f23,plain,(
% 1.26/0.54    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.26/0.54    inference(ennf_transformation,[],[f15])).
% 1.26/0.54  fof(f15,axiom,(
% 1.26/0.54    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 1.26/0.54  fof(f111,plain,(
% 1.26/0.54    spl9_1),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f110])).
% 1.26/0.54  fof(f110,plain,(
% 1.26/0.54    $false | spl9_1),
% 1.26/0.54    inference(subsumption_resolution,[],[f109,f81])).
% 1.26/0.54  fof(f81,plain,(
% 1.26/0.54    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl9_1),
% 1.26/0.54    inference(avatar_component_clause,[],[f79])).
% 1.26/0.54  fof(f109,plain,(
% 1.26/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.26/0.54    inference(resolution,[],[f97,f47])).
% 1.26/0.54  fof(f97,plain,(
% 1.26/0.54    v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 1.26/0.54    inference(resolution,[],[f90,f49])).
% 1.26/0.54  fof(f90,plain,(
% 1.26/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 1.26/0.54    inference(resolution,[],[f89,f77])).
% 1.26/0.54  fof(f77,plain,(
% 1.26/0.54    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 1.26/0.54    inference(equality_resolution,[],[f58])).
% 1.26/0.54  fof(f58,plain,(
% 1.26/0.54    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.26/0.54    inference(cnf_transformation,[],[f43])).
% 1.26/0.54  fof(f43,plain,(
% 1.26/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f39,f42,f41,f40])).
% 1.26/0.54  fof(f40,plain,(
% 1.26/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f41,plain,(
% 1.26/0.54    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f42,plain,(
% 1.26/0.54    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f39,plain,(
% 1.26/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.26/0.54    inference(rectify,[],[f38])).
% 1.26/0.54  fof(f38,plain,(
% 1.26/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.26/0.54    inference(nnf_transformation,[],[f14])).
% 1.26/0.54  fof(f14,axiom,(
% 1.26/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.26/0.54  fof(f86,plain,(
% 1.26/0.54    ~spl9_1 | ~spl9_2),
% 1.26/0.54    inference(avatar_split_clause,[],[f44,f83,f79])).
% 1.26/0.54  fof(f44,plain,(
% 1.26/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.26/0.54    inference(cnf_transformation,[],[f19])).
% 1.26/0.54  fof(f19,plain,(
% 1.26/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.26/0.54    inference(ennf_transformation,[],[f17])).
% 1.26/0.54  fof(f17,negated_conjecture,(
% 1.26/0.54    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 1.26/0.54    inference(negated_conjecture,[],[f16])).
% 1.26/0.54  fof(f16,conjecture,(
% 1.26/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.26/0.54  % SZS output end Proof for theBenchmark
% 1.26/0.54  % (20577)------------------------------
% 1.26/0.54  % (20577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (20577)Termination reason: Refutation
% 1.26/0.54  
% 1.26/0.54  % (20577)Memory used [KB]: 10746
% 1.26/0.54  % (20577)Time elapsed: 0.113 s
% 1.26/0.54  % (20577)------------------------------
% 1.26/0.54  % (20577)------------------------------
% 1.40/0.54  % (20573)Success in time 0.176 s
%------------------------------------------------------------------------------
