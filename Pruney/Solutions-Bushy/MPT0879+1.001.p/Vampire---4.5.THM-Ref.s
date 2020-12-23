%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0879+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  39 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f24,f29])).

% (31204)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f29,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f25])).

fof(f25,plain,
    ( $false
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f10,f23])).

fof(f23,plain,
    ( k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) != k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl3_2
  <=> k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) = k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f10,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f24,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f19,f15,f21])).

fof(f15,plain,
    ( spl3_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) = k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f19,plain,
    ( k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) != k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(sK2))
    | spl3_1 ),
    inference(backward_demodulation,[],[f17,f10])).

fof(f17,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f18,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f13,f15])).

fof(f13,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f9,f12,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f9,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2))
   => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

%------------------------------------------------------------------------------
