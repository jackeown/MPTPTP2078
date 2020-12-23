%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t141_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:01 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  83 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f59,f66,f74,f99,f104])).

fof(f104,plain,
    ( spl2_3
    | spl2_9 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f100,f98])).

fof(f98,plain,
    ( k4_xboole_0(sK1,k1_tarski(sK0)) != sK1
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_9
  <=> k4_xboole_0(sK1,k1_tarski(sK0)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f100,plain,
    ( k4_xboole_0(sK1,k1_tarski(sK0)) = sK1
    | ~ spl2_3 ),
    inference(resolution,[],[f42,f58])).

fof(f58,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_3
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
     => k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t141_zfmisc_1.p',t65_zfmisc_1)).

fof(f99,plain,
    ( ~ spl2_9
    | spl2_7 ),
    inference(avatar_split_clause,[],[f88,f72,f97])).

fof(f72,plain,
    ( spl2_7
  <=> k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f88,plain,
    ( k4_xboole_0(sK1,k1_tarski(sK0)) != sK1
    | ~ spl2_7 ),
    inference(superposition,[],[f73,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t141_zfmisc_1.p',t40_xboole_1)).

fof(f73,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
    & ~ r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & ~ r2_hidden(X0,X1) )
   => ( k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
      & ~ r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t141_zfmisc_1.p',t141_zfmisc_1)).

fof(f66,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f64,plain,
    ( spl2_4
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f33,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t141_zfmisc_1.p',d2_xboole_0)).

fof(f59,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f45,f50])).

fof(f50,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f32,f33])).

fof(f32,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t141_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
