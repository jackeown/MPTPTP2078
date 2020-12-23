%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:50 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 188 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  334 ( 530 expanded)
%              Number of equality atoms :   89 ( 181 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f82,f98,f107,f117,f121,f135,f226,f241,f281])).

fof(f281,plain,
    ( ~ spl1_1
    | spl1_6
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl1_1
    | spl1_6
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f279,f81])).

fof(f81,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl1_6
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f279,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f278,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f278,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f277,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f277,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))
    | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f276,f47])).

fof(f276,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0),k5_relat_1(sK0,k1_xboole_0))
    | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f275,f52])).

fof(f52,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f275,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0),k5_relat_1(sK0,k1_xboole_0))
    | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f266,f93])).

fof(f93,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl1_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f266,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0),k5_relat_1(sK0,k1_xboole_0))
    | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_11 ),
    inference(superposition,[],[f191,f134])).

fof(f134,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl1_11
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f191,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2))),k5_relat_1(X1,X2))
      | k5_relat_1(X1,X2) = k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f73,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f73,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) = X2
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X2) ) ),
    inference(resolution,[],[f41,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f241,plain,
    ( spl1_5
    | ~ spl1_9
    | ~ spl1_19 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl1_5
    | ~ spl1_9
    | ~ spl1_19 ),
    inference(subsumption_resolution,[],[f239,f33])).

fof(f239,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0))
    | spl1_5
    | ~ spl1_9
    | ~ spl1_19 ),
    inference(forward_demodulation,[],[f238,f48])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f238,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0))
    | spl1_5
    | ~ spl1_9
    | ~ spl1_19 ),
    inference(forward_demodulation,[],[f237,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl1_9
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f237,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0))
    | spl1_5
    | ~ spl1_9
    | ~ spl1_19 ),
    inference(subsumption_resolution,[],[f236,f77])).

fof(f77,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl1_5
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f236,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_9
    | ~ spl1_19 ),
    inference(forward_demodulation,[],[f235,f48])).

fof(f235,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_9
    | ~ spl1_19 ),
    inference(forward_demodulation,[],[f232,f116])).

fof(f232,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_19 ),
    inference(resolution,[],[f209,f73])).

fof(f209,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl1_19
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f226,plain,
    ( ~ spl1_1
    | ~ spl1_7
    | spl1_19 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_7
    | spl1_19 ),
    inference(subsumption_resolution,[],[f224,f93])).

fof(f224,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_1
    | spl1_19 ),
    inference(subsumption_resolution,[],[f221,f52])).

fof(f221,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_19 ),
    inference(resolution,[],[f210,f38])).

fof(f210,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_19 ),
    inference(avatar_component_clause,[],[f208])).

fof(f135,plain,
    ( spl1_11
    | ~ spl1_1
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f130,f119,f50,f132])).

fof(f119,plain,
    ( spl1_10
  <=> ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f130,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_10 ),
    inference(resolution,[],[f120,f52])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl1_10
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f112,f92,f65,f60,f119])).

fof(f60,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f65,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f112,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f102,f93])).

fof(f102,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f101,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f101,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f99,f33])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3 ),
    inference(superposition,[],[f37,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f117,plain,
    ( spl1_9
    | ~ spl1_1
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f111,f96,f50,f114])).

fof(f96,plain,
    ( spl1_8
  <=> ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f111,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_1
    | ~ spl1_8 ),
    inference(resolution,[],[f97,f52])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f107,plain,
    ( ~ spl1_2
    | spl1_7 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl1_2
    | spl1_7 ),
    inference(subsumption_resolution,[],[f104,f57])).

fof(f57,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f104,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_7 ),
    inference(resolution,[],[f94,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f94,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f98,plain,
    ( ~ spl1_7
    | spl1_8
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f90,f65,f60,f96,f92])).

fof(f90,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f89,f62])).

fof(f89,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f87,f33])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4 ),
    inference(superposition,[],[f36,f67])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f82,plain,
    ( ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f29,f79,f75])).

fof(f29,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f68,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f32,f65])).

fof(f32,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f63,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f53,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (812089344)
% 0.13/0.36  ipcrm: permission denied for id (814088194)
% 0.13/0.37  ipcrm: permission denied for id (812122115)
% 0.13/0.37  ipcrm: permission denied for id (814252040)
% 0.13/0.37  ipcrm: permission denied for id (814284809)
% 0.13/0.37  ipcrm: permission denied for id (817594378)
% 0.13/0.37  ipcrm: permission denied for id (817627147)
% 0.13/0.38  ipcrm: permission denied for id (814383116)
% 0.13/0.38  ipcrm: permission denied for id (817692686)
% 0.13/0.38  ipcrm: permission denied for id (817725455)
% 0.13/0.38  ipcrm: permission denied for id (814514192)
% 0.13/0.38  ipcrm: permission denied for id (817790993)
% 0.13/0.38  ipcrm: permission denied for id (814579730)
% 0.13/0.38  ipcrm: permission denied for id (812351507)
% 0.13/0.39  ipcrm: permission denied for id (814645269)
% 0.13/0.39  ipcrm: permission denied for id (814678038)
% 0.13/0.39  ipcrm: permission denied for id (812384279)
% 0.13/0.39  ipcrm: permission denied for id (814710808)
% 0.13/0.39  ipcrm: permission denied for id (814743577)
% 0.13/0.39  ipcrm: permission denied for id (814809115)
% 0.13/0.40  ipcrm: permission denied for id (812417052)
% 0.13/0.40  ipcrm: permission denied for id (814841885)
% 0.13/0.40  ipcrm: permission denied for id (812449822)
% 0.13/0.40  ipcrm: permission denied for id (817889311)
% 0.13/0.40  ipcrm: permission denied for id (817954848)
% 0.13/0.40  ipcrm: permission denied for id (814940193)
% 0.13/0.40  ipcrm: permission denied for id (812515362)
% 0.13/0.40  ipcrm: permission denied for id (814972963)
% 0.13/0.41  ipcrm: permission denied for id (812580902)
% 0.21/0.41  ipcrm: permission denied for id (818053159)
% 0.21/0.41  ipcrm: permission denied for id (815136809)
% 0.21/0.41  ipcrm: permission denied for id (812646442)
% 0.21/0.41  ipcrm: permission denied for id (815169579)
% 0.21/0.41  ipcrm: permission denied for id (815202348)
% 0.21/0.42  ipcrm: permission denied for id (815235117)
% 0.21/0.42  ipcrm: permission denied for id (815267886)
% 0.21/0.42  ipcrm: permission denied for id (815366193)
% 0.21/0.42  ipcrm: permission denied for id (812744754)
% 0.21/0.42  ipcrm: permission denied for id (818184243)
% 0.21/0.42  ipcrm: permission denied for id (815431732)
% 0.21/0.43  ipcrm: permission denied for id (818249782)
% 0.21/0.43  ipcrm: permission denied for id (812843063)
% 0.21/0.43  ipcrm: permission denied for id (815530040)
% 0.21/0.43  ipcrm: permission denied for id (815562809)
% 0.21/0.43  ipcrm: permission denied for id (815595578)
% 0.21/0.43  ipcrm: permission denied for id (818282555)
% 0.21/0.43  ipcrm: permission denied for id (815661116)
% 0.21/0.44  ipcrm: permission denied for id (818315325)
% 0.21/0.44  ipcrm: permission denied for id (815726654)
% 0.21/0.44  ipcrm: permission denied for id (813039680)
% 0.21/0.44  ipcrm: permission denied for id (818413634)
% 0.21/0.44  ipcrm: permission denied for id (813105219)
% 0.21/0.44  ipcrm: permission denied for id (815857732)
% 0.21/0.45  ipcrm: permission denied for id (813137989)
% 0.21/0.45  ipcrm: permission denied for id (813170759)
% 0.21/0.45  ipcrm: permission denied for id (813203528)
% 0.21/0.45  ipcrm: permission denied for id (815956042)
% 0.21/0.45  ipcrm: permission denied for id (815988811)
% 0.21/0.45  ipcrm: permission denied for id (816021580)
% 0.21/0.45  ipcrm: permission denied for id (818511949)
% 0.21/0.46  ipcrm: permission denied for id (813269070)
% 0.21/0.46  ipcrm: permission denied for id (813301839)
% 0.21/0.46  ipcrm: permission denied for id (818544720)
% 0.21/0.46  ipcrm: permission denied for id (816185426)
% 0.21/0.46  ipcrm: permission denied for id (816218195)
% 0.21/0.46  ipcrm: permission denied for id (818610260)
% 0.21/0.46  ipcrm: permission denied for id (816283733)
% 0.21/0.47  ipcrm: permission denied for id (813367382)
% 0.21/0.47  ipcrm: permission denied for id (816316503)
% 0.21/0.47  ipcrm: permission denied for id (816382041)
% 0.21/0.47  ipcrm: permission denied for id (818675802)
% 0.21/0.47  ipcrm: permission denied for id (816447579)
% 0.21/0.47  ipcrm: permission denied for id (818708572)
% 0.21/0.47  ipcrm: permission denied for id (816513117)
% 0.21/0.48  ipcrm: permission denied for id (818806880)
% 0.21/0.48  ipcrm: permission denied for id (813498466)
% 0.21/0.48  ipcrm: permission denied for id (816709732)
% 0.21/0.49  ipcrm: permission denied for id (813596774)
% 0.21/0.49  ipcrm: permission denied for id (818937959)
% 0.21/0.49  ipcrm: permission denied for id (816840808)
% 0.21/0.49  ipcrm: permission denied for id (818970729)
% 0.21/0.49  ipcrm: permission denied for id (819003498)
% 0.21/0.49  ipcrm: permission denied for id (816939115)
% 0.21/0.49  ipcrm: permission denied for id (813727853)
% 0.21/0.50  ipcrm: permission denied for id (819069038)
% 0.21/0.50  ipcrm: permission denied for id (813760623)
% 0.21/0.50  ipcrm: permission denied for id (817102962)
% 0.21/0.50  ipcrm: permission denied for id (813826164)
% 0.21/0.50  ipcrm: permission denied for id (813858933)
% 0.21/0.51  ipcrm: permission denied for id (817168502)
% 0.21/0.51  ipcrm: permission denied for id (819232888)
% 0.21/0.51  ipcrm: permission denied for id (817332347)
% 0.21/0.51  ipcrm: permission denied for id (813957244)
% 0.21/0.51  ipcrm: permission denied for id (819363965)
% 0.21/0.51  ipcrm: permission denied for id (817397886)
% 0.21/0.52  ipcrm: permission denied for id (814022783)
% 1.01/0.63  % (20019)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.01/0.63  % (20024)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.01/0.63  % (20039)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.01/0.64  % (20019)Refutation found. Thanks to Tanya!
% 1.01/0.64  % SZS status Theorem for theBenchmark
% 1.01/0.64  % SZS output start Proof for theBenchmark
% 1.01/0.64  fof(f286,plain,(
% 1.01/0.64    $false),
% 1.01/0.64    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f82,f98,f107,f117,f121,f135,f226,f241,f281])).
% 1.01/0.64  fof(f281,plain,(
% 1.01/0.64    ~spl1_1 | spl1_6 | ~spl1_7 | ~spl1_11),
% 1.01/0.64    inference(avatar_contradiction_clause,[],[f280])).
% 1.01/0.64  fof(f280,plain,(
% 1.01/0.64    $false | (~spl1_1 | spl1_6 | ~spl1_7 | ~spl1_11)),
% 1.01/0.64    inference(subsumption_resolution,[],[f279,f81])).
% 1.01/0.64  fof(f81,plain,(
% 1.01/0.64    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_6),
% 1.01/0.64    inference(avatar_component_clause,[],[f79])).
% 1.01/0.64  fof(f79,plain,(
% 1.01/0.64    spl1_6 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.01/0.64  fof(f279,plain,(
% 1.01/0.64    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_1 | ~spl1_7 | ~spl1_11)),
% 1.01/0.64    inference(forward_demodulation,[],[f278,f47])).
% 1.01/0.64  fof(f47,plain,(
% 1.01/0.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.01/0.64    inference(equality_resolution,[],[f44])).
% 1.01/0.64  fof(f44,plain,(
% 1.01/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.01/0.64    inference(cnf_transformation,[],[f27])).
% 1.01/0.64  fof(f27,plain,(
% 1.01/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.01/0.64    inference(flattening,[],[f26])).
% 1.01/0.64  fof(f26,plain,(
% 1.01/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.01/0.64    inference(nnf_transformation,[],[f4])).
% 1.01/0.64  fof(f4,axiom,(
% 1.01/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.01/0.64  fof(f278,plain,(
% 1.01/0.64    k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | (~spl1_1 | ~spl1_7 | ~spl1_11)),
% 1.01/0.64    inference(subsumption_resolution,[],[f277,f33])).
% 1.01/0.64  fof(f33,plain,(
% 1.01/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.01/0.64    inference(cnf_transformation,[],[f3])).
% 1.01/0.64  fof(f3,axiom,(
% 1.01/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.01/0.64  fof(f277,plain,(
% 1.01/0.64    ~r1_tarski(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | (~spl1_1 | ~spl1_7 | ~spl1_11)),
% 1.01/0.64    inference(forward_demodulation,[],[f276,f47])).
% 1.01/0.64  fof(f276,plain,(
% 1.01/0.64    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | (~spl1_1 | ~spl1_7 | ~spl1_11)),
% 1.01/0.64    inference(subsumption_resolution,[],[f275,f52])).
% 1.01/0.64  fof(f52,plain,(
% 1.01/0.64    v1_relat_1(sK0) | ~spl1_1),
% 1.01/0.64    inference(avatar_component_clause,[],[f50])).
% 1.01/0.64  fof(f50,plain,(
% 1.01/0.64    spl1_1 <=> v1_relat_1(sK0)),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.01/0.64  fof(f275,plain,(
% 1.01/0.64    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(sK0) | (~spl1_7 | ~spl1_11)),
% 1.01/0.64    inference(subsumption_resolution,[],[f266,f93])).
% 1.01/0.64  fof(f93,plain,(
% 1.01/0.64    v1_relat_1(k1_xboole_0) | ~spl1_7),
% 1.01/0.64    inference(avatar_component_clause,[],[f92])).
% 1.01/0.64  fof(f92,plain,(
% 1.01/0.64    spl1_7 <=> v1_relat_1(k1_xboole_0)),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 1.01/0.64  fof(f266,plain,(
% 1.01/0.64    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | ~spl1_11),
% 1.01/0.64    inference(superposition,[],[f191,f134])).
% 1.01/0.64  fof(f134,plain,(
% 1.01/0.64    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_11),
% 1.01/0.64    inference(avatar_component_clause,[],[f132])).
% 1.01/0.64  fof(f132,plain,(
% 1.01/0.64    spl1_11 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 1.01/0.64  fof(f191,plain,(
% 1.01/0.64    ( ! [X2,X1] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2))),k5_relat_1(X1,X2)) | k5_relat_1(X1,X2) = k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2))) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.01/0.64    inference(resolution,[],[f73,f38])).
% 1.01/0.64  fof(f38,plain,(
% 1.01/0.64    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.01/0.64    inference(cnf_transformation,[],[f21])).
% 1.01/0.64  fof(f21,plain,(
% 1.01/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.01/0.64    inference(flattening,[],[f20])).
% 1.01/0.64  fof(f20,plain,(
% 1.01/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.01/0.64    inference(ennf_transformation,[],[f6])).
% 1.01/0.64  fof(f6,axiom,(
% 1.01/0.64    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.01/0.64  fof(f73,plain,(
% 1.01/0.64    ( ! [X2] : (~v1_relat_1(X2) | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) = X2 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X2)) )),
% 1.01/0.64    inference(resolution,[],[f41,f35])).
% 1.01/0.64  fof(f35,plain,(
% 1.01/0.64    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.01/0.64    inference(cnf_transformation,[],[f15])).
% 1.01/0.64  fof(f15,plain,(
% 1.01/0.64    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.01/0.64    inference(ennf_transformation,[],[f7])).
% 1.01/0.64  fof(f7,axiom,(
% 1.01/0.64    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.01/0.64  fof(f41,plain,(
% 1.01/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.01/0.64    inference(cnf_transformation,[],[f25])).
% 1.01/0.64  fof(f25,plain,(
% 1.01/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.01/0.64    inference(flattening,[],[f24])).
% 1.01/0.64  fof(f24,plain,(
% 1.01/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.01/0.64    inference(nnf_transformation,[],[f2])).
% 1.01/0.64  fof(f2,axiom,(
% 1.01/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.01/0.64  fof(f241,plain,(
% 1.01/0.64    spl1_5 | ~spl1_9 | ~spl1_19),
% 1.01/0.64    inference(avatar_contradiction_clause,[],[f240])).
% 1.01/0.64  fof(f240,plain,(
% 1.01/0.64    $false | (spl1_5 | ~spl1_9 | ~spl1_19)),
% 1.01/0.64    inference(subsumption_resolution,[],[f239,f33])).
% 1.01/0.64  fof(f239,plain,(
% 1.01/0.64    ~r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) | (spl1_5 | ~spl1_9 | ~spl1_19)),
% 1.01/0.64    inference(forward_demodulation,[],[f238,f48])).
% 1.01/0.64  fof(f48,plain,(
% 1.01/0.64    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.01/0.64    inference(equality_resolution,[],[f43])).
% 1.01/0.64  fof(f43,plain,(
% 1.01/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.01/0.64    inference(cnf_transformation,[],[f27])).
% 1.01/0.64  fof(f238,plain,(
% 1.01/0.64    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) | (spl1_5 | ~spl1_9 | ~spl1_19)),
% 1.01/0.64    inference(forward_demodulation,[],[f237,f116])).
% 1.01/0.64  fof(f116,plain,(
% 1.01/0.64    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_9),
% 1.01/0.64    inference(avatar_component_clause,[],[f114])).
% 1.01/0.64  fof(f114,plain,(
% 1.01/0.64    spl1_9 <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 1.01/0.64  fof(f237,plain,(
% 1.01/0.64    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) | (spl1_5 | ~spl1_9 | ~spl1_19)),
% 1.01/0.64    inference(subsumption_resolution,[],[f236,f77])).
% 1.01/0.64  fof(f77,plain,(
% 1.01/0.64    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_5),
% 1.01/0.64    inference(avatar_component_clause,[],[f75])).
% 1.01/0.64  fof(f75,plain,(
% 1.01/0.64    spl1_5 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.01/0.64  fof(f236,plain,(
% 1.01/0.64    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) | (~spl1_9 | ~spl1_19)),
% 1.01/0.64    inference(forward_demodulation,[],[f235,f48])).
% 1.01/0.64  fof(f235,plain,(
% 1.01/0.64    k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) | (~spl1_9 | ~spl1_19)),
% 1.01/0.64    inference(forward_demodulation,[],[f232,f116])).
% 1.01/0.64  fof(f232,plain,(
% 1.01/0.64    k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) | ~spl1_19),
% 1.01/0.64    inference(resolution,[],[f209,f73])).
% 1.01/0.64  fof(f209,plain,(
% 1.01/0.64    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_19),
% 1.01/0.64    inference(avatar_component_clause,[],[f208])).
% 1.01/0.64  fof(f208,plain,(
% 1.01/0.64    spl1_19 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 1.01/0.64  fof(f226,plain,(
% 1.01/0.64    ~spl1_1 | ~spl1_7 | spl1_19),
% 1.01/0.64    inference(avatar_contradiction_clause,[],[f225])).
% 1.01/0.64  fof(f225,plain,(
% 1.01/0.64    $false | (~spl1_1 | ~spl1_7 | spl1_19)),
% 1.01/0.64    inference(subsumption_resolution,[],[f224,f93])).
% 1.01/0.64  fof(f224,plain,(
% 1.01/0.64    ~v1_relat_1(k1_xboole_0) | (~spl1_1 | spl1_19)),
% 1.01/0.64    inference(subsumption_resolution,[],[f221,f52])).
% 1.01/0.64  fof(f221,plain,(
% 1.01/0.64    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_19),
% 1.01/0.64    inference(resolution,[],[f210,f38])).
% 1.01/0.64  fof(f210,plain,(
% 1.01/0.64    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_19),
% 1.01/0.64    inference(avatar_component_clause,[],[f208])).
% 1.01/0.64  fof(f135,plain,(
% 1.01/0.64    spl1_11 | ~spl1_1 | ~spl1_10),
% 1.01/0.64    inference(avatar_split_clause,[],[f130,f119,f50,f132])).
% 1.01/0.64  fof(f119,plain,(
% 1.01/0.64    spl1_10 <=> ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 1.01/0.64  fof(f130,plain,(
% 1.01/0.64    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_1 | ~spl1_10)),
% 1.01/0.64    inference(resolution,[],[f120,f52])).
% 1.01/0.64  fof(f120,plain,(
% 1.01/0.64    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) ) | ~spl1_10),
% 1.01/0.64    inference(avatar_component_clause,[],[f119])).
% 1.01/0.64  fof(f121,plain,(
% 1.01/0.64    spl1_10 | ~spl1_3 | ~spl1_4 | ~spl1_7),
% 1.01/0.64    inference(avatar_split_clause,[],[f112,f92,f65,f60,f119])).
% 1.01/0.64  fof(f60,plain,(
% 1.01/0.64    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.01/0.64  fof(f65,plain,(
% 1.01/0.64    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.01/0.64  fof(f112,plain,(
% 1.01/0.64    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_7)),
% 1.01/0.64    inference(subsumption_resolution,[],[f102,f93])).
% 1.01/0.64  fof(f102,plain,(
% 1.01/0.64    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_3 | ~spl1_4)),
% 1.01/0.64    inference(forward_demodulation,[],[f101,f67])).
% 1.01/0.64  fof(f67,plain,(
% 1.01/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 1.01/0.64    inference(avatar_component_clause,[],[f65])).
% 1.01/0.64  fof(f101,plain,(
% 1.01/0.64    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_3),
% 1.01/0.64    inference(subsumption_resolution,[],[f99,f33])).
% 1.01/0.64  fof(f99,plain,(
% 1.01/0.64    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_3),
% 1.01/0.64    inference(superposition,[],[f37,f62])).
% 1.01/0.64  fof(f62,plain,(
% 1.01/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 1.01/0.64    inference(avatar_component_clause,[],[f60])).
% 1.01/0.64  fof(f37,plain,(
% 1.01/0.64    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.01/0.64    inference(cnf_transformation,[],[f19])).
% 1.01/0.64  fof(f19,plain,(
% 1.01/0.64    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.01/0.64    inference(flattening,[],[f18])).
% 1.01/0.64  fof(f18,plain,(
% 1.01/0.64    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.01/0.64    inference(ennf_transformation,[],[f9])).
% 1.01/0.64  fof(f9,axiom,(
% 1.01/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 1.01/0.64  fof(f117,plain,(
% 1.01/0.64    spl1_9 | ~spl1_1 | ~spl1_8),
% 1.01/0.64    inference(avatar_split_clause,[],[f111,f96,f50,f114])).
% 1.01/0.64  fof(f96,plain,(
% 1.01/0.64    spl1_8 <=> ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0))),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 1.01/0.64  fof(f111,plain,(
% 1.01/0.64    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_1 | ~spl1_8)),
% 1.01/0.64    inference(resolution,[],[f97,f52])).
% 1.01/0.64  fof(f97,plain,(
% 1.01/0.64    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_8),
% 1.01/0.64    inference(avatar_component_clause,[],[f96])).
% 1.01/0.64  fof(f107,plain,(
% 1.01/0.64    ~spl1_2 | spl1_7),
% 1.01/0.64    inference(avatar_contradiction_clause,[],[f106])).
% 1.01/0.64  fof(f106,plain,(
% 1.01/0.64    $false | (~spl1_2 | spl1_7)),
% 1.01/0.64    inference(subsumption_resolution,[],[f104,f57])).
% 1.01/0.64  fof(f57,plain,(
% 1.01/0.64    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 1.01/0.64    inference(avatar_component_clause,[],[f55])).
% 1.01/0.64  fof(f55,plain,(
% 1.01/0.64    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 1.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.01/0.64  fof(f104,plain,(
% 1.01/0.64    ~v1_xboole_0(k1_xboole_0) | spl1_7),
% 1.01/0.64    inference(resolution,[],[f94,f34])).
% 1.01/0.64  fof(f34,plain,(
% 1.01/0.64    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.01/0.64    inference(cnf_transformation,[],[f14])).
% 1.01/0.64  fof(f14,plain,(
% 1.01/0.64    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.01/0.64    inference(ennf_transformation,[],[f5])).
% 1.01/0.64  fof(f5,axiom,(
% 1.01/0.64    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.01/0.64  fof(f94,plain,(
% 1.01/0.64    ~v1_relat_1(k1_xboole_0) | spl1_7),
% 1.01/0.64    inference(avatar_component_clause,[],[f92])).
% 1.01/0.64  fof(f98,plain,(
% 1.01/0.64    ~spl1_7 | spl1_8 | ~spl1_3 | ~spl1_4),
% 1.01/0.64    inference(avatar_split_clause,[],[f90,f65,f60,f96,f92])).
% 1.01/0.64  fof(f90,plain,(
% 1.01/0.64    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_3 | ~spl1_4)),
% 1.01/0.64    inference(forward_demodulation,[],[f89,f62])).
% 1.01/0.64  fof(f89,plain,(
% 1.01/0.64    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_4),
% 1.01/0.64    inference(subsumption_resolution,[],[f87,f33])).
% 1.01/0.64  fof(f87,plain,(
% 1.01/0.64    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_4),
% 1.01/0.64    inference(superposition,[],[f36,f67])).
% 1.01/0.64  fof(f36,plain,(
% 1.01/0.64    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.01/0.64    inference(cnf_transformation,[],[f17])).
% 1.01/0.64  fof(f17,plain,(
% 1.01/0.64    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.01/0.64    inference(flattening,[],[f16])).
% 1.01/0.64  fof(f16,plain,(
% 1.01/0.64    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.01/0.64    inference(ennf_transformation,[],[f8])).
% 1.01/0.64  fof(f8,axiom,(
% 1.01/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.01/0.64  fof(f82,plain,(
% 1.01/0.64    ~spl1_5 | ~spl1_6),
% 1.01/0.64    inference(avatar_split_clause,[],[f29,f79,f75])).
% 1.01/0.64  fof(f29,plain,(
% 1.01/0.64    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.01/0.64    inference(cnf_transformation,[],[f23])).
% 1.01/0.64  fof(f23,plain,(
% 1.01/0.64    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.01/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f22])).
% 1.01/0.64  fof(f22,plain,(
% 1.01/0.64    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.01/0.64    introduced(choice_axiom,[])).
% 1.01/0.64  fof(f13,plain,(
% 1.01/0.64    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.01/0.64    inference(ennf_transformation,[],[f12])).
% 1.01/0.64  fof(f12,negated_conjecture,(
% 1.01/0.64    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.01/0.64    inference(negated_conjecture,[],[f11])).
% 1.01/0.64  fof(f11,conjecture,(
% 1.01/0.64    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.01/0.64  fof(f68,plain,(
% 1.01/0.64    spl1_4),
% 1.01/0.64    inference(avatar_split_clause,[],[f32,f65])).
% 1.01/0.64  fof(f32,plain,(
% 1.01/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.01/0.64    inference(cnf_transformation,[],[f10])).
% 1.01/0.64  fof(f10,axiom,(
% 1.01/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.01/0.64  fof(f63,plain,(
% 1.01/0.64    spl1_3),
% 1.01/0.64    inference(avatar_split_clause,[],[f31,f60])).
% 1.01/0.64  fof(f31,plain,(
% 1.01/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.01/0.64    inference(cnf_transformation,[],[f10])).
% 1.01/0.64  fof(f58,plain,(
% 1.01/0.64    spl1_2),
% 1.01/0.64    inference(avatar_split_clause,[],[f30,f55])).
% 1.01/0.64  fof(f30,plain,(
% 1.01/0.64    v1_xboole_0(k1_xboole_0)),
% 1.01/0.64    inference(cnf_transformation,[],[f1])).
% 1.01/0.64  fof(f1,axiom,(
% 1.01/0.64    v1_xboole_0(k1_xboole_0)),
% 1.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.01/0.64  fof(f53,plain,(
% 1.01/0.64    spl1_1),
% 1.01/0.64    inference(avatar_split_clause,[],[f28,f50])).
% 1.01/0.64  fof(f28,plain,(
% 1.01/0.64    v1_relat_1(sK0)),
% 1.01/0.64    inference(cnf_transformation,[],[f23])).
% 1.01/0.64  % SZS output end Proof for theBenchmark
% 1.01/0.64  % (20019)------------------------------
% 1.01/0.64  % (20019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.01/0.64  % (20019)Termination reason: Refutation
% 1.01/0.64  
% 1.01/0.64  % (20019)Memory used [KB]: 6268
% 1.01/0.64  % (20019)Time elapsed: 0.077 s
% 1.01/0.64  % (20019)------------------------------
% 1.01/0.64  % (20019)------------------------------
% 1.01/0.64  % (19865)Success in time 0.282 s
%------------------------------------------------------------------------------
