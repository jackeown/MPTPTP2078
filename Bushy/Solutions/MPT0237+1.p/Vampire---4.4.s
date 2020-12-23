%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t32_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:05 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  37 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f53,f70,f80])).

fof(f80,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f78,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t32_zfmisc_1.p',t41_enumset1)).

fof(f78,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl2_5 ),
    inference(superposition,[],[f69,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t32_zfmisc_1.p',l51_zfmisc_1)).

fof(f69,plain,
    ( k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_5
  <=> k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f70,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).

fof(f26,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t32_zfmisc_1.p',t32_zfmisc_1)).

fof(f53,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f30,f51])).

fof(f51,plain,
    ( spl2_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f30,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t32_zfmisc_1.p',d2_xboole_0)).

fof(f46,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f39,f44])).

fof(f44,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f29,f30])).

fof(f29,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t32_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
