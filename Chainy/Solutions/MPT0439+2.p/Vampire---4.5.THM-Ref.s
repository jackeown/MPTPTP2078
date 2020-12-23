%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0439+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:30 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   27 (  36 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  72 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1078,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f871,f875,f1072,f1077])).

fof(f1077,plain,
    ( spl13_1
    | ~ spl13_5 ),
    inference(avatar_contradiction_clause,[],[f1076])).

fof(f1076,plain,
    ( $false
    | spl13_1
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f1074,f870])).

fof(f870,plain,
    ( sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f869])).

fof(f869,plain,
    ( spl13_1
  <=> sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f1074,plain,
    ( sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl13_5 ),
    inference(resolution,[],[f1071,f784])).

fof(f784,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f678])).

fof(f678,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1071,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1070,plain,
    ( spl13_5
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f1072,plain,
    ( spl13_5
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f1068,f873,f1070])).

fof(f873,plain,
    ( spl13_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f1068,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl13_2 ),
    inference(resolution,[],[f845,f874])).

fof(f874,plain,
    ( v1_relat_1(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f873])).

fof(f845,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f709])).

fof(f709,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f655])).

fof(f655,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f875,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f748,f873])).

fof(f748,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f718])).

fof(f718,plain,
    ( sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f661,f717])).

fof(f717,plain,
    ( ? [X0] :
        ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f661,plain,(
    ? [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f657])).

fof(f657,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(negated_conjecture,[],[f656])).

fof(f656,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f871,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f749,f869])).

fof(f749,plain,(
    sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f718])).
%------------------------------------------------------------------------------
