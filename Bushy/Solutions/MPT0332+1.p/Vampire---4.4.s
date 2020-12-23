%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t145_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:02 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 133 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f61,f68,f75,f92,f116,f133])).

fof(f133,plain,
    ( spl3_3
    | spl3_5
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f131,f115])).

fof(f115,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_11
  <=> k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f131,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) = sK2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f128,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t145_zfmisc_1.p',commutativity_k2_tarski)).

fof(f128,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK1,sK0)) = sK2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f117,f67])).

fof(f67,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_5
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f117,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | k4_xboole_0(sK2,k2_tarski(X0,sK0)) = sK2 )
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f60])).

fof(f60,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_3
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t145_zfmisc_1.p',t144_zfmisc_1)).

fof(f116,plain,
    ( ~ spl3_11
    | spl3_9 ),
    inference(avatar_split_clause,[],[f109,f90,f114])).

fof(f90,plain,
    ( spl3_9
  <=> k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f109,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2
    | ~ spl3_9 ),
    inference(superposition,[],[f91,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t145_zfmisc_1.p',t40_xboole_1)).

fof(f91,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f32,f90])).

fof(f32,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t145_zfmisc_1.p',t145_zfmisc_1)).

fof(f75,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f73,plain,
    ( spl3_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f34,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t145_zfmisc_1.p',d2_xboole_0)).

fof(f68,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f47,f52])).

fof(f52,plain,
    ( spl3_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f33,f34])).

fof(f33,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t145_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
