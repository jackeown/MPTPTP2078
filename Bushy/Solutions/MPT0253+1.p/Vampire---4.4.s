%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t48_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:08 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 102 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :  127 ( 238 expanded)
%              Number of equality atoms :   21 (  41 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f61,f68,f75,f84,f93,f100,f117,f133,f143,f148])).

fof(f148,plain,
    ( spl3_9
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f146,f83])).

fof(f83,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_9
  <=> k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f146,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK2),sK1) = sK1
    | ~ spl3_18 ),
    inference(resolution,[],[f142,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t48_zfmisc_1.p',t12_xboole_1)).

fof(f142,plain,
    ( r1_tarski(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_18
  <=> r1_tarski(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f143,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f126,f66,f59,f141])).

fof(f59,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f66,plain,
    ( spl3_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f126,plain,
    ( r1_tarski(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f123,f67])).

fof(f67,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k2_tarski(sK0,X0),sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f46,f60])).

fof(f60,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t48_zfmisc_1.p',t38_zfmisc_1)).

fof(f133,plain,
    ( spl3_16
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f125,f59,f131])).

fof(f131,plain,
    ( spl3_16
  <=> r1_tarski(k2_tarski(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f125,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f123,f60])).

fof(f117,plain,
    ( ~ spl3_15
    | spl3_9 ),
    inference(avatar_split_clause,[],[f104,f82,f115])).

fof(f115,plain,
    ( spl3_15
  <=> k2_xboole_0(sK1,k2_tarski(sK0,sK2)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f104,plain,
    ( k2_xboole_0(sK1,k2_tarski(sK0,sK2)) != sK1
    | ~ spl3_9 ),
    inference(superposition,[],[f83,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t48_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(f100,plain,
    ( ~ spl3_13
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f86,f66,f98])).

fof(f98,plain,
    ( spl3_13
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f86,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f41,f67])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t48_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f93,plain,
    ( ~ spl3_11
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f85,f59,f91])).

fof(f91,plain,
    ( spl3_11
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f85,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f60])).

fof(f84,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t48_zfmisc_1.p',t48_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t48_zfmisc_1.p',d2_xboole_0)).

fof(f68,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t48_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
