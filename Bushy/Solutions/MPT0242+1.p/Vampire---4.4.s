%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t37_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:06 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  105 ( 153 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f45,f59,f67,f68,f76,f79,f82])).

fof(f82,plain,
    ( ~ spl2_4
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f80,f55])).

fof(f55,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_7
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f80,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f52,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t37_zfmisc_1.p',l1_zfmisc_1)).

fof(f52,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_4
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f79,plain,
    ( spl2_5
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f77,f49])).

fof(f49,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_5
  <=> ~ r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f77,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_6 ),
    inference(resolution,[],[f28,f58])).

fof(f58,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_6
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,
    ( ~ spl2_11
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f69,f57,f74])).

fof(f74,plain,
    ( spl2_11
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f69,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f26,f58])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t37_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f68,plain,
    ( ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f22,f54,f48])).

fof(f22,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | ~ r1_tarski(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | r1_tarski(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | ~ r1_tarski(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | r1_tarski(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | ~ r1_tarski(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | r1_tarski(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t37_zfmisc_1.p',t37_zfmisc_1)).

fof(f67,plain,
    ( ~ spl2_9
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f60,f57,f65])).

fof(f65,plain,
    ( spl2_9
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f60,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl2_6 ),
    inference(resolution,[],[f58,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t37_zfmisc_1.p',t7_boole)).

fof(f59,plain,
    ( spl2_4
    | spl2_6 ),
    inference(avatar_split_clause,[],[f21,f57,f51])).

fof(f21,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f43,plain,
    ( spl2_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f24,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t37_zfmisc_1.p',d2_xboole_0)).

fof(f38,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f23,f36])).

fof(f36,plain,
    ( spl2_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f23,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t37_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
