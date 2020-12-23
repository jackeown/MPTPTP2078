%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t50_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:08 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   88 ( 122 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f52,f60,f71,f79,f88,f98,f104])).

fof(f104,plain,
    ( ~ spl3_0
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f101,f44])).

fof(f44,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f101,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_12 ),
    inference(superposition,[],[f32,f97])).

fof(f97,plain,
    ( k2_tarski(sK0,sK1) = k1_xboole_0
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_12
  <=> k2_tarski(sK0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f32,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t50_zfmisc_1.p',fc3_xboole_0)).

fof(f98,plain,
    ( spl3_12
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f89,f86,f96])).

fof(f86,plain,
    ( spl3_10
  <=> k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f89,plain,
    ( k2_tarski(sK0,sK1) = k1_xboole_0
    | ~ spl3_10 ),
    inference(superposition,[],[f87,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t50_zfmisc_1.p',t1_boole)).

fof(f87,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k1_xboole_0
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f81,f77,f58,f86])).

fof(f58,plain,
    ( spl3_4
  <=> k2_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f77,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f81,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k1_xboole_0
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f59,f78])).

fof(f78,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f59,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f79,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f72,f69,f77])).

fof(f69,plain,
    ( spl3_6
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f72,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_6 ),
    inference(resolution,[],[f70,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t50_zfmisc_1.p',t6_boole)).

fof(f70,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,
    ( spl3_6
    | ~ spl3_0
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f64,f58,f43,f69])).

fof(f64,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_0
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f63,f44])).

fof(f63,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f36,f59])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t50_zfmisc_1.p',fc5_xboole_0)).

fof(f60,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
   => k2_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t50_zfmisc_1.p',t50_zfmisc_1)).

fof(f52,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f50,plain,
    ( spl3_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f29,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t50_zfmisc_1.p',d2_xboole_0)).

fof(f45,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f38,f43])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f28,f29])).

fof(f28,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t50_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
