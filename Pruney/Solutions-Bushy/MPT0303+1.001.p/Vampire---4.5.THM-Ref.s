%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0303+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  69 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 153 expanded)
%              Number of equality atoms :   12 (  44 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f139,f184,f201])).

fof(f201,plain,
    ( ~ spl3_1
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl3_1
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f9,f86,f21,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f21,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_1
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f86,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_5
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f9,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(f184,plain,
    ( ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl3_2
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f172,f86,f24])).

fof(f24,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl3_2
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f172,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f9,f86,f10])).

fof(f139,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f87,f87,f114,f17])).

fof(f17,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK0))
      | ~ r2_hidden(X4,sK1) ) ),
    inference(superposition,[],[f14,f8])).

fof(f8,plain,(
    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f114,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK2(sK0,sK1),X0),k2_zfmisc_1(sK0,X1))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f92,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f92,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f9,f87,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f25,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f18,f23,f20])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f15,f14])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f12,f8])).

%------------------------------------------------------------------------------
