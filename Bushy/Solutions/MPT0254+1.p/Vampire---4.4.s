%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t49_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:08 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   88 ( 122 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f50,f57,f69,f77,f86,f96,f102])).

fof(f102,plain,
    ( ~ spl2_0
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f99,f42])).

fof(f42,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_0 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f99,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl2_12 ),
    inference(superposition,[],[f29,f95])).

fof(f95,plain,
    ( k1_tarski(sK0) = k1_xboole_0
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl2_12
  <=> k1_tarski(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t49_zfmisc_1.p',fc2_xboole_0)).

fof(f96,plain,
    ( spl2_12
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f87,f84,f94])).

fof(f84,plain,
    ( spl2_10
  <=> k2_xboole_0(k1_tarski(sK0),k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f87,plain,
    ( k1_tarski(sK0) = k1_xboole_0
    | ~ spl2_10 ),
    inference(superposition,[],[f85,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t49_zfmisc_1.p',t1_boole)).

fof(f85,plain,
    ( k2_xboole_0(k1_tarski(sK0),k1_xboole_0) = k1_xboole_0
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f79,f75,f55,f84])).

fof(f55,plain,
    ( spl2_4
  <=> k2_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f75,plain,
    ( spl2_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f79,plain,
    ( k2_xboole_0(k1_tarski(sK0),k1_xboole_0) = k1_xboole_0
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(superposition,[],[f56,f76])).

fof(f76,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f56,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f77,plain,
    ( spl2_8
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f70,f67,f75])).

fof(f67,plain,
    ( spl2_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_6 ),
    inference(resolution,[],[f68,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t49_zfmisc_1.p',t6_boole)).

fof(f68,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,
    ( spl2_6
    | ~ spl2_0
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f62,f55,f41,f67])).

fof(f62,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_0
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f61,f42])).

fof(f61,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK1)
    | ~ spl2_4 ),
    inference(superposition,[],[f34,f56])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t49_zfmisc_1.p',fc5_xboole_0)).

fof(f57,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f24])).

fof(f24,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
   => k2_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t49_zfmisc_1.p',t49_zfmisc_1)).

fof(f50,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f28,f48])).

fof(f48,plain,
    ( spl2_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f28,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t49_zfmisc_1.p',d2_xboole_0)).

fof(f43,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f36,f41])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f27,f28])).

fof(f27,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t49_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
