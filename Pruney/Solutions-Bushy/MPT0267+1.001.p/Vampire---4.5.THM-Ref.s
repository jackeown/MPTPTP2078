%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0267+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  72 expanded)
%              Number of leaves         :    8 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :  107 ( 172 expanded)
%              Number of equality atoms :   20 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f39,f68,f74,f81,f84,f90])).

fof(f90,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f87,f65,f30])).

fof(f30,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f65,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f87,plain,
    ( sK0 = sK2
    | ~ spl5_4 ),
    inference(resolution,[],[f67,f19])).

fof(f19,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f10])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f67,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f84,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f28,f82])).

fof(f82,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(sK1,X0))
    | spl5_3 ),
    inference(resolution,[],[f36,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f36,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f28,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f81,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f21,f73,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f73,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_5
  <=> r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f21,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f9])).

fof(f9,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f74,plain,
    ( spl5_5
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f69,f30,f26,f71])).

fof(f69,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f28,f31])).

fof(f31,plain,
    ( sK0 = sK2
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f68,plain,
    ( ~ spl5_3
    | spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f54,f26,f65,f35])).

fof(f54,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | ~ r2_hidden(sK0,sK1)
    | spl5_1 ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f39,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f6,f35,f30,f26])).

fof(f6,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f38,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f7,f35,f26])).

fof(f7,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f8,f30,f26])).

fof(f8,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
