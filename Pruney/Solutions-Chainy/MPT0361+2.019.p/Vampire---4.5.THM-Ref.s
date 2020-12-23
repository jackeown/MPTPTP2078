%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 109 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 274 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f76,f80,f92,f103,f116,f127])).

fof(f127,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f125,f35])).

fof(f35,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f125,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f124,f45])).

fof(f45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f124,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_9 ),
    inference(subsumption_resolution,[],[f123,f24])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f123,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_9 ),
    inference(superposition,[],[f102,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f102,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_9
  <=> r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f116,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | spl3_8 ),
    inference(subsumption_resolution,[],[f114,f35])).

fof(f114,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3
    | spl3_8 ),
    inference(subsumption_resolution,[],[f113,f45])).

fof(f113,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_8 ),
    inference(resolution,[],[f91,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f30,f31])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f91,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_8
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f103,plain,
    ( ~ spl3_9
    | ~ spl3_1
    | spl3_6 ),
    inference(avatar_split_clause,[],[f98,f69,f33,f100])).

fof(f69,plain,
    ( spl3_6
  <=> r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k4_subset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f98,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))
    | ~ spl3_1
    | spl3_6 ),
    inference(subsumption_resolution,[],[f96,f35])).

fof(f96,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_6 ),
    inference(superposition,[],[f71,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f71,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k4_subset_1(sK0,sK1,sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f92,plain,
    ( ~ spl3_8
    | ~ spl3_1
    | ~ spl3_3
    | spl3_7 ),
    inference(avatar_split_clause,[],[f87,f73,f43,f33,f89])).

fof(f73,plain,
    ( spl3_7
  <=> m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_3
    | spl3_7 ),
    inference(subsumption_resolution,[],[f86,f35])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3
    | spl3_7 ),
    inference(subsumption_resolution,[],[f82,f45])).

fof(f82,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_7 ),
    inference(superposition,[],[f75,f31])).

fof(f75,plain,
    ( ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f80,plain,
    ( ~ spl3_1
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl3_1
    | spl3_5 ),
    inference(subsumption_resolution,[],[f78,f35])).

fof(f78,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_5 ),
    inference(resolution,[],[f67,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f67,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_5
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f76,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | spl3_2 ),
    inference(avatar_split_clause,[],[f62,f38,f73,f69,f65])).

fof(f38,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k4_subset_1(sK0,sK1,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl3_2 ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(f46,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f41,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f23,f33])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:07:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (9373)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.45  % (9367)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.45  % (9368)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.45  % (9376)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.45  % (9367)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f128,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f36,f41,f46,f76,f80,f92,f103,f116,f127])).
% 0.20/0.45  fof(f127,plain,(
% 0.20/0.45    ~spl3_1 | ~spl3_3 | spl3_9),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f126])).
% 0.20/0.45  fof(f126,plain,(
% 0.20/0.45    $false | (~spl3_1 | ~spl3_3 | spl3_9)),
% 0.20/0.45    inference(subsumption_resolution,[],[f125,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.45  fof(f125,plain,(
% 0.20/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_3 | spl3_9)),
% 0.20/0.45    inference(subsumption_resolution,[],[f124,f45])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.45  fof(f124,plain,(
% 0.20/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_9),
% 0.20/0.45    inference(subsumption_resolution,[],[f123,f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.45  fof(f123,plain,(
% 0.20/0.45    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_9),
% 0.20/0.45    inference(superposition,[],[f102,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(flattening,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.45  fof(f102,plain,(
% 0.20/0.45    ~r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) | spl3_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f100])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    spl3_9 <=> r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.45  fof(f116,plain,(
% 0.20/0.45    ~spl3_1 | ~spl3_3 | spl3_8),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f115])).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    $false | (~spl3_1 | ~spl3_3 | spl3_8)),
% 0.20/0.45    inference(subsumption_resolution,[],[f114,f35])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_3 | spl3_8)),
% 0.20/0.45    inference(subsumption_resolution,[],[f113,f45])).
% 0.20/0.45  fof(f113,plain,(
% 0.20/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_8),
% 0.20/0.45    inference(resolution,[],[f91,f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f53])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(superposition,[],[f30,f31])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(flattening,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl3_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f89])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    spl3_8 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    ~spl3_9 | ~spl3_1 | spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f98,f69,f33,f100])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    spl3_6 <=> r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k4_subset_1(sK0,sK1,sK2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    ~r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) | (~spl3_1 | spl3_6)),
% 0.20/0.45    inference(subsumption_resolution,[],[f96,f35])).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    ~r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_6),
% 0.20/0.45    inference(superposition,[],[f71,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ~r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k4_subset_1(sK0,sK1,sK2)) | spl3_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f69])).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    ~spl3_8 | ~spl3_1 | ~spl3_3 | spl3_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f87,f73,f43,f33,f89])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    spl3_7 <=> m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | (~spl3_1 | ~spl3_3 | spl3_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f86,f35])).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_3 | spl3_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f82,f45])).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_7),
% 0.20/0.45    inference(superposition,[],[f75,f31])).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | spl3_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f73])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    ~spl3_1 | spl3_5),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f79])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    $false | (~spl3_1 | spl3_5)),
% 0.20/0.45    inference(subsumption_resolution,[],[f78,f35])).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_5),
% 0.20/0.45    inference(resolution,[],[f67,f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl3_5 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ~spl3_5 | ~spl3_6 | ~spl3_7 | spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f62,f38,f73,f69,f65])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    spl3_2 <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | ~r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k4_subset_1(sK0,sK1,sK2)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl3_2),
% 0.20/0.46    inference(resolution,[],[f29,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) | spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f38])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(flattening,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : ((r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f43])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.20/0.46    inference(negated_conjecture,[],[f9])).
% 0.20/0.46  fof(f9,conjecture,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ~spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f38])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f33])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (9367)------------------------------
% 0.20/0.46  % (9367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9367)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (9367)Memory used [KB]: 10618
% 0.20/0.46  % (9367)Time elapsed: 0.011 s
% 0.20/0.46  % (9367)------------------------------
% 0.20/0.46  % (9367)------------------------------
% 0.20/0.46  % (9365)Success in time 0.102 s
%------------------------------------------------------------------------------
