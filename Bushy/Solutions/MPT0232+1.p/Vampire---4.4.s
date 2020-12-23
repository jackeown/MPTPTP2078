%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t27_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:04 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  67 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 126 expanded)
%              Number of equality atoms :   24 (  41 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f40,f47,f60,f67,f74,f84])).

fof(f84,plain,
    ( spl3_7
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f81,f25])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t27_zfmisc_1.p',t69_enumset1)).

fof(f81,plain,
    ( k2_tarski(sK0,sK0) != k1_tarski(sK0)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f76,f59])).

fof(f59,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_7
  <=> k2_tarski(sK0,sK1) != k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f76,plain,
    ( sK0 = sK1
    | ~ spl3_8 ),
    inference(resolution,[],[f50,f66])).

fof(f66,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_8
  <=> r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f50,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k2_tarski(X3,X2),k1_tarski(X4))
      | X2 = X4 ) ),
    inference(superposition,[],[f21,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t27_zfmisc_1.p',commutativity_k2_tarski)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t27_zfmisc_1.p',t26_zfmisc_1)).

fof(f74,plain,
    ( spl3_10
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f48,f31,f72])).

fof(f72,plain,
    ( spl3_10
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f31,plain,
    ( spl3_0
  <=> r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f48,plain,
    ( sK0 = sK2
    | ~ spl3_0 ),
    inference(resolution,[],[f21,f32])).

fof(f32,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f31])).

fof(f67,plain,
    ( spl3_8
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f53,f31,f65])).

fof(f53,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK0))
    | ~ spl3_0 ),
    inference(backward_demodulation,[],[f48,f32])).

fof(f60,plain,
    ( ~ spl3_7
    | ~ spl3_0
    | spl3_3 ),
    inference(avatar_split_clause,[],[f52,f38,f31,f58])).

fof(f38,plain,
    ( spl3_3
  <=> k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f52,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK0)
    | ~ spl3_0
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f48,f39])).

fof(f39,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f45])).

fof(f45,plain,
    ( spl3_4
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f26,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t27_zfmisc_1.p',d2_xboole_0)).

fof(f40,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f20,f38])).

fof(f20,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t27_zfmisc_1.p',t27_zfmisc_1)).

fof(f33,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f19,f31])).

fof(f19,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
