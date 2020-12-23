%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t46_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:07 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   39 (  52 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   68 (  96 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f52,f59,f66,f76,f93,f97])).

fof(f97,plain,
    ( ~ spl2_2
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f95,f65])).

fof(f65,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_7
  <=> k2_xboole_0(k1_tarski(sK0),sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f95,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) = sK1
    | ~ spl2_2 ),
    inference(resolution,[],[f34,f51])).

fof(f51,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t46_zfmisc_1.p',l22_zfmisc_1)).

fof(f93,plain,
    ( ~ spl2_11
    | spl2_7 ),
    inference(avatar_split_clause,[],[f80,f64,f91])).

fof(f91,plain,
    ( spl2_11
  <=> k2_xboole_0(sK1,k1_tarski(sK0)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f80,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK0)) != sK1
    | ~ spl2_7 ),
    inference(superposition,[],[f65,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t46_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(f76,plain,
    ( ~ spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f69,f50,f74])).

fof(f74,plain,
    ( spl2_9
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f69,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f33,f51])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t46_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f66,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t46_zfmisc_1.p',t46_zfmisc_1)).

fof(f59,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f57,plain,
    ( spl2_4
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f28,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t46_zfmisc_1.p',d2_xboole_0)).

fof(f52,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f27,f43])).

fof(f43,plain,
    ( spl2_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f27,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t46_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
