%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:08 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 149 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  195 ( 275 expanded)
%              Number of equality atoms :   80 ( 138 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f115,f125,f127,f137])).

fof(f137,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f132])).

fof(f132,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_4 ),
    inference(superposition,[],[f37,f112])).

fof(f112,plain,
    ( k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_4
  <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f37,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(f127,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f124,f38])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f124,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f125,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | spl4_3 ),
    inference(avatar_split_clause,[],[f120,f106,f122,f97])).

fof(f97,plain,
    ( spl4_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f106,plain,
    ( spl4_3
  <=> v1_relat_1(k8_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f120,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl4_3 ),
    inference(resolution,[],[f108,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X1,X0))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc18_relat_1)).

fof(f108,plain,
    ( ~ v1_relat_1(k8_relat_1(k1_xboole_0,sK0))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f115,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f99,f36])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f99,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f113,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f95,f110,f106])).

fof(f95,plain,
    ( k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k8_relat_1(k1_xboole_0,sK0)) ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k8_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f41,f85])).

fof(f85,plain,(
    k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f83,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f83,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k8_relat_1(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f82,f36])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(k1_xboole_0,X1))) ) ),
    inference(resolution,[],[f80,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f78,f70])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X2)) ) ),
    inference(resolution,[],[f76,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK2(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK2(X1,X2,X3),sK3(X1,X2,X3)) = X3
        & r2_hidden(sK3(X1,X2,X3),X2)
        & r2_hidden(sK2(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f34])).

fof(f34,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK2(X1,X2,X3),sK3(X1,X2,X3)) = X3
        & r2_hidden(sK3(X1,X2,X3),X2)
        & r2_hidden(sK2(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f76,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,(
    ! [X2] :
      ( k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f67,f71])).

fof(f71,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f65,f64])).

fof(f64,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f63,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f61])).

fof(f39,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(f65,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f44,f63,f45,f63,f62])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f54,f62,f62])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:03:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (28917)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (28930)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.17/0.51  % (28934)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.17/0.52  % (28911)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.53  % (28913)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.53  % (28912)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  % (28932)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.53  % (28912)Refutation not found, incomplete strategy% (28912)------------------------------
% 1.30/0.53  % (28912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (28912)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (28912)Memory used [KB]: 10618
% 1.30/0.53  % (28912)Time elapsed: 0.115 s
% 1.30/0.53  % (28912)------------------------------
% 1.30/0.53  % (28912)------------------------------
% 1.30/0.54  % (28937)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.54  % (28926)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.30/0.54  % (28914)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.54  % (28920)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.54  % (28924)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.54  % (28915)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.54  % (28918)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.30/0.54  % (28920)Refutation not found, incomplete strategy% (28920)------------------------------
% 1.30/0.54  % (28920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (28920)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (28922)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.54  % (28920)Memory used [KB]: 10618
% 1.30/0.54  % (28920)Time elapsed: 0.129 s
% 1.30/0.54  % (28920)------------------------------
% 1.30/0.54  % (28920)------------------------------
% 1.30/0.55  % (28922)Refutation found. Thanks to Tanya!
% 1.30/0.55  % SZS status Theorem for theBenchmark
% 1.30/0.55  % (28935)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.55  % (28940)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.55  % (28936)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.55  % (28916)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.55  % (28938)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.55  % (28919)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.30/0.55  % (28910)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.55  % (28910)Refutation not found, incomplete strategy% (28910)------------------------------
% 1.30/0.55  % (28910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (28910)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (28910)Memory used [KB]: 1663
% 1.30/0.55  % (28910)Time elapsed: 0.143 s
% 1.30/0.55  % (28910)------------------------------
% 1.30/0.55  % (28910)------------------------------
% 1.30/0.56  % (28919)Refutation not found, incomplete strategy% (28919)------------------------------
% 1.30/0.56  % (28919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (28919)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (28919)Memory used [KB]: 10618
% 1.30/0.56  % (28919)Time elapsed: 0.146 s
% 1.30/0.56  % (28919)------------------------------
% 1.30/0.56  % (28919)------------------------------
% 1.30/0.56  % (28927)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.56  % (28927)Refutation not found, incomplete strategy% (28927)------------------------------
% 1.30/0.56  % (28927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (28927)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (28927)Memory used [KB]: 10618
% 1.30/0.56  % (28927)Time elapsed: 0.159 s
% 1.30/0.56  % (28927)------------------------------
% 1.30/0.56  % (28927)------------------------------
% 1.30/0.56  % (28925)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.30/0.57  % SZS output start Proof for theBenchmark
% 1.30/0.57  fof(f139,plain,(
% 1.30/0.57    $false),
% 1.30/0.57    inference(avatar_sat_refutation,[],[f113,f115,f125,f127,f137])).
% 1.30/0.57  fof(f137,plain,(
% 1.30/0.57    ~spl4_4),
% 1.30/0.57    inference(avatar_contradiction_clause,[],[f136])).
% 1.30/0.57  fof(f136,plain,(
% 1.30/0.57    $false | ~spl4_4),
% 1.30/0.57    inference(trivial_inequality_removal,[],[f132])).
% 1.30/0.57  fof(f132,plain,(
% 1.30/0.57    k1_xboole_0 != k1_xboole_0 | ~spl4_4),
% 1.30/0.57    inference(superposition,[],[f37,f112])).
% 1.30/0.57  fof(f112,plain,(
% 1.30/0.57    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) | ~spl4_4),
% 1.30/0.57    inference(avatar_component_clause,[],[f110])).
% 1.30/0.57  fof(f110,plain,(
% 1.30/0.57    spl4_4 <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)),
% 1.30/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.30/0.57  fof(f37,plain,(
% 1.30/0.57    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)),
% 1.30/0.57    inference(cnf_transformation,[],[f27])).
% 1.30/0.57  fof(f27,plain,(
% 1.30/0.57    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0)),
% 1.30/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f26])).
% 1.30/0.57  fof(f26,plain,(
% 1.30/0.57    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0)) => (k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0))),
% 1.30/0.57    introduced(choice_axiom,[])).
% 1.30/0.57  fof(f18,plain,(
% 1.30/0.57    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0))),
% 1.30/0.57    inference(ennf_transformation,[],[f17])).
% 1.30/0.57  fof(f17,negated_conjecture,(
% 1.30/0.57    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 1.30/0.57    inference(negated_conjecture,[],[f16])).
% 1.30/0.57  fof(f16,conjecture,(
% 1.30/0.57    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).
% 1.30/0.57  fof(f127,plain,(
% 1.30/0.57    spl4_5),
% 1.30/0.57    inference(avatar_contradiction_clause,[],[f126])).
% 1.30/0.57  fof(f126,plain,(
% 1.30/0.57    $false | spl4_5),
% 1.30/0.57    inference(resolution,[],[f124,f38])).
% 1.30/0.57  fof(f38,plain,(
% 1.30/0.57    v1_xboole_0(k1_xboole_0)),
% 1.30/0.57    inference(cnf_transformation,[],[f1])).
% 1.30/0.57  fof(f1,axiom,(
% 1.30/0.57    v1_xboole_0(k1_xboole_0)),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.30/0.57  fof(f124,plain,(
% 1.30/0.57    ~v1_xboole_0(k1_xboole_0) | spl4_5),
% 1.30/0.57    inference(avatar_component_clause,[],[f122])).
% 1.30/0.57  fof(f122,plain,(
% 1.30/0.57    spl4_5 <=> v1_xboole_0(k1_xboole_0)),
% 1.30/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.30/0.57  fof(f125,plain,(
% 1.30/0.57    ~spl4_1 | ~spl4_5 | spl4_3),
% 1.30/0.57    inference(avatar_split_clause,[],[f120,f106,f122,f97])).
% 1.30/0.57  fof(f97,plain,(
% 1.30/0.57    spl4_1 <=> v1_relat_1(sK0)),
% 1.30/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.30/0.57  fof(f106,plain,(
% 1.30/0.57    spl4_3 <=> v1_relat_1(k8_relat_1(k1_xboole_0,sK0))),
% 1.30/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.30/0.57  fof(f120,plain,(
% 1.30/0.57    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | spl4_3),
% 1.30/0.57    inference(resolution,[],[f108,f49])).
% 1.30/0.57  fof(f49,plain,(
% 1.30/0.57    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,X0)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f24])).
% 1.30/0.57  fof(f24,plain,(
% 1.30/0.57    ! [X0,X1] : ((v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 1.30/0.57    inference(flattening,[],[f23])).
% 1.30/0.57  fof(f23,plain,(
% 1.30/0.57    ! [X0,X1] : ((v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 1.30/0.57    inference(ennf_transformation,[],[f13])).
% 1.30/0.57  fof(f13,axiom,(
% 1.30/0.57    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc18_relat_1)).
% 1.30/0.57  fof(f108,plain,(
% 1.30/0.57    ~v1_relat_1(k8_relat_1(k1_xboole_0,sK0)) | spl4_3),
% 1.30/0.57    inference(avatar_component_clause,[],[f106])).
% 1.30/0.57  fof(f115,plain,(
% 1.30/0.57    spl4_1),
% 1.30/0.57    inference(avatar_contradiction_clause,[],[f114])).
% 1.30/0.57  fof(f114,plain,(
% 1.30/0.57    $false | spl4_1),
% 1.30/0.57    inference(resolution,[],[f99,f36])).
% 1.30/0.57  fof(f36,plain,(
% 1.30/0.57    v1_relat_1(sK0)),
% 1.30/0.57    inference(cnf_transformation,[],[f27])).
% 1.30/0.57  fof(f99,plain,(
% 1.30/0.57    ~v1_relat_1(sK0) | spl4_1),
% 1.30/0.57    inference(avatar_component_clause,[],[f97])).
% 1.30/0.57  fof(f113,plain,(
% 1.30/0.57    ~spl4_3 | spl4_4),
% 1.30/0.57    inference(avatar_split_clause,[],[f95,f110,f106])).
% 1.30/0.57  fof(f95,plain,(
% 1.30/0.57    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k8_relat_1(k1_xboole_0,sK0))),
% 1.30/0.57    inference(trivial_inequality_removal,[],[f94])).
% 1.30/0.57  fof(f94,plain,(
% 1.30/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k8_relat_1(k1_xboole_0,sK0))),
% 1.30/0.57    inference(superposition,[],[f41,f85])).
% 1.30/0.57  fof(f85,plain,(
% 1.30/0.57    k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK0))),
% 1.30/0.57    inference(resolution,[],[f83,f42])).
% 1.30/0.57  fof(f42,plain,(
% 1.30/0.57    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.30/0.57    inference(cnf_transformation,[],[f29])).
% 1.30/0.57  fof(f29,plain,(
% 1.30/0.57    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 1.30/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f28])).
% 1.30/0.57  fof(f28,plain,(
% 1.30/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.30/0.57    introduced(choice_axiom,[])).
% 1.30/0.57  fof(f21,plain,(
% 1.30/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.30/0.57    inference(ennf_transformation,[],[f2])).
% 1.30/0.57  fof(f2,axiom,(
% 1.30/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.30/0.57  fof(f83,plain,(
% 1.30/0.57    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k8_relat_1(k1_xboole_0,sK0)))) )),
% 1.30/0.57    inference(resolution,[],[f82,f36])).
% 1.30/0.57  fof(f82,plain,(
% 1.30/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(k1_xboole_0,X1)))) )),
% 1.30/0.57    inference(resolution,[],[f80,f47])).
% 1.30/0.57  fof(f47,plain,(
% 1.30/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f22])).
% 1.30/0.57  fof(f22,plain,(
% 1.30/0.57    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 1.30/0.57    inference(ennf_transformation,[],[f14])).
% 1.30/0.57  fof(f14,axiom,(
% 1.30/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 1.30/0.57  fof(f80,plain,(
% 1.30/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.30/0.57    inference(forward_demodulation,[],[f78,f70])).
% 1.30/0.57  fof(f70,plain,(
% 1.30/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.30/0.57    inference(equality_resolution,[],[f51])).
% 1.30/0.57  fof(f51,plain,(
% 1.30/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.30/0.57    inference(cnf_transformation,[],[f31])).
% 1.30/0.57  fof(f31,plain,(
% 1.30/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.30/0.57    inference(flattening,[],[f30])).
% 1.30/0.57  fof(f30,plain,(
% 1.30/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.30/0.57    inference(nnf_transformation,[],[f9])).
% 1.30/0.57  fof(f9,axiom,(
% 1.30/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.30/0.57  fof(f78,plain,(
% 1.30/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X2))) )),
% 1.30/0.57    inference(resolution,[],[f76,f57])).
% 1.30/0.57  fof(f57,plain,(
% 1.30/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(sK2(X1,X2,X3),X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 1.30/0.57    inference(cnf_transformation,[],[f35])).
% 1.30/0.57  fof(f35,plain,(
% 1.30/0.57    ! [X0,X1,X2,X3] : ((k4_tarski(sK2(X1,X2,X3),sK3(X1,X2,X3)) = X3 & r2_hidden(sK3(X1,X2,X3),X2) & r2_hidden(sK2(X1,X2,X3),X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.30/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f34])).
% 1.30/0.57  fof(f34,plain,(
% 1.30/0.57    ! [X3,X2,X1] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) => (k4_tarski(sK2(X1,X2,X3),sK3(X1,X2,X3)) = X3 & r2_hidden(sK3(X1,X2,X3),X2) & r2_hidden(sK2(X1,X2,X3),X1)))),
% 1.30/0.57    introduced(choice_axiom,[])).
% 1.30/0.57  fof(f25,plain,(
% 1.30/0.57    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.30/0.57    inference(ennf_transformation,[],[f8])).
% 1.30/0.57  fof(f8,axiom,(
% 1.30/0.57    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 1.30/0.57  fof(f76,plain,(
% 1.30/0.57    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 1.30/0.57    inference(trivial_inequality_removal,[],[f75])).
% 1.30/0.57  fof(f75,plain,(
% 1.30/0.57    ( ! [X2] : (k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != k5_enumset1(X2,X2,X2,X2,X2,X2,X2) | ~r2_hidden(X2,k1_xboole_0)) )),
% 1.30/0.57    inference(superposition,[],[f67,f71])).
% 1.30/0.57  fof(f71,plain,(
% 1.30/0.57    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_xboole_0)) )),
% 1.30/0.57    inference(forward_demodulation,[],[f65,f64])).
% 1.30/0.57  fof(f64,plain,(
% 1.30/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.30/0.57    inference(definition_unfolding,[],[f43,f63,f62])).
% 1.30/0.57  fof(f62,plain,(
% 1.30/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.30/0.57    inference(definition_unfolding,[],[f46,f61])).
% 1.30/0.57  fof(f61,plain,(
% 1.30/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.30/0.57    inference(definition_unfolding,[],[f56,f60])).
% 1.30/0.57  fof(f60,plain,(
% 1.30/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f4])).
% 1.30/0.57  fof(f4,axiom,(
% 1.30/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.30/0.57  fof(f56,plain,(
% 1.30/0.57    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f6])).
% 1.30/0.57  fof(f6,axiom,(
% 1.30/0.57    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).
% 1.30/0.57  fof(f46,plain,(
% 1.30/0.57    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f5])).
% 1.30/0.57  fof(f5,axiom,(
% 1.30/0.57    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 1.30/0.57  fof(f63,plain,(
% 1.30/0.57    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.30/0.57    inference(definition_unfolding,[],[f39,f61])).
% 1.30/0.57  fof(f39,plain,(
% 1.30/0.57    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f7])).
% 1.30/0.57  fof(f7,axiom,(
% 1.30/0.57    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 1.30/0.57  fof(f43,plain,(
% 1.30/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.30/0.57    inference(cnf_transformation,[],[f11])).
% 1.30/0.57  fof(f11,axiom,(
% 1.30/0.57    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).
% 1.30/0.57  fof(f65,plain,(
% 1.30/0.57    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.30/0.57    inference(definition_unfolding,[],[f44,f63,f45,f63,f62])).
% 1.30/0.57  fof(f45,plain,(
% 1.30/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f3])).
% 1.30/0.57  fof(f3,axiom,(
% 1.30/0.57    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.30/0.57  fof(f44,plain,(
% 1.30/0.57    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.30/0.57    inference(cnf_transformation,[],[f10])).
% 1.30/0.57  fof(f10,axiom,(
% 1.30/0.57    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 1.30/0.57  fof(f67,plain,(
% 1.30/0.57    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 1.30/0.57    inference(definition_unfolding,[],[f54,f62,f62])).
% 1.30/0.57  fof(f54,plain,(
% 1.30/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f33])).
% 1.30/0.57  fof(f33,plain,(
% 1.30/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.30/0.57    inference(flattening,[],[f32])).
% 1.30/0.57  fof(f32,plain,(
% 1.30/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.30/0.57    inference(nnf_transformation,[],[f12])).
% 1.30/0.57  fof(f12,axiom,(
% 1.30/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.30/0.57  fof(f41,plain,(
% 1.30/0.57    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f20])).
% 1.30/0.57  fof(f20,plain,(
% 1.30/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.30/0.57    inference(flattening,[],[f19])).
% 1.30/0.57  fof(f19,plain,(
% 1.30/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.30/0.57    inference(ennf_transformation,[],[f15])).
% 1.30/0.57  fof(f15,axiom,(
% 1.30/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.30/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.30/0.57  % SZS output end Proof for theBenchmark
% 1.30/0.57  % (28922)------------------------------
% 1.30/0.57  % (28922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.57  % (28922)Termination reason: Refutation
% 1.30/0.57  
% 1.30/0.57  % (28922)Memory used [KB]: 6268
% 1.30/0.57  % (28922)Time elapsed: 0.149 s
% 1.30/0.57  % (28922)------------------------------
% 1.30/0.57  % (28922)------------------------------
% 1.30/0.57  % (28928)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.57  % (28909)Success in time 0.206 s
%------------------------------------------------------------------------------
