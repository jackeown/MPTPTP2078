%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0318+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:44 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   30 (  65 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 ( 110 expanded)
%              Number of equality atoms :   32 (  81 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f59,f66])).

fof(f66,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f64,f14])).

fof(f14,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f64,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f13,f60])).

fof(f60,plain,
    ( o_0_0_xboole_0 = k1_tarski(sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f16,f26,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f10,f15,f15,f15])).

fof(f15,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f26,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> o_0_0_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f16,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f9,f15])).

fof(f9,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f13,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f59,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f55,f14])).

fof(f55,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f13,f50])).

fof(f50,plain,
    ( o_0_0_xboole_0 = k1_tarski(sK1)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f16,f30,f20])).

fof(f30,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_2
  <=> o_0_0_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f31,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f17,f28,f24])).

fof(f17,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(definition_unfolding,[],[f8,f15,f15])).

fof(f8,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
