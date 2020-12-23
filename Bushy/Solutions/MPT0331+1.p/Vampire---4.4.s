%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t144_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:01 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 134 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f58,f65,f72,f80,f113])).

fof(f113,plain,
    ( spl3_3
    | spl3_5
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f109,f79])).

fof(f79,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_9
  <=> k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f109,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) = sK2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f98,f64])).

fof(f64,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_5
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f98,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | k4_xboole_0(sK2,k2_tarski(sK0,X0)) = sK2 )
    | ~ spl3_3 ),
    inference(resolution,[],[f94,f57])).

fof(f57,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_3
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | k4_xboole_0(X1,k2_tarski(X0,X2)) = X1 ) ),
    inference(resolution,[],[f91,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t144_zfmisc_1.p',t83_xboole_1)).

fof(f91,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(X4,k2_tarski(X5,X3))
      | r2_hidden(X5,X4)
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t144_zfmisc_1.p',symmetry_r1_xboole_0)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t144_zfmisc_1.p',l168_zfmisc_1)).

fof(f80,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f30,f78])).

fof(f30,plain,(
    k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t144_zfmisc_1.p',t144_zfmisc_1)).

fof(f72,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f70,plain,
    ( spl3_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f32,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t144_zfmisc_1.p',d2_xboole_0)).

fof(f65,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f44,f49])).

fof(f49,plain,
    ( spl3_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f31,f32])).

fof(f31,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t144_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
