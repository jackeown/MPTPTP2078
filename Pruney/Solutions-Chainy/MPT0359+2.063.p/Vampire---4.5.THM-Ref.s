%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 306 expanded)
%              Number of leaves         :   17 (  88 expanded)
%              Depth                    :   17
%              Number of atoms          :  198 ( 767 expanded)
%              Number of equality atoms :   63 ( 313 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f86,f113,f118,f134,f137,f143])).

fof(f143,plain,
    ( spl4_2
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f141,f79])).

fof(f79,plain,
    ( sK0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f141,plain,
    ( sK0 = sK1
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f139,f63])).

fof(f63,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f139,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f121,f133])).

fof(f133,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_7
  <=> k1_xboole_0 = k3_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f121,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f38,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

% (31637)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f29,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f137,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f135,f38])).

fof(f135,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_6 ),
    inference(resolution,[],[f129,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f129,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_6
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f134,plain,
    ( ~ spl4_6
    | spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f125,f83,f131,f127])).

fof(f83,plain,
    ( spl4_3
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f125,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f123,f85])).

fof(f85,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f123,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f67,f121])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f41])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f118,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f116,f111])).

fof(f111,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f108,f63])).

fof(f108,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(resolution,[],[f107,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f107,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f96,f88])).

fof(f88,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f38,f78])).

fof(f78,plain,
    ( sK0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f96,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(superposition,[],[f52,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f91,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f91,plain,
    ( k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f90,f48])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f90,plain,
    ( k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f88,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f116,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f75,f92])).

fof(f75,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_1
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f113,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f111,f94])).

fof(f94,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl4_2
    | spl4_3 ),
    inference(backward_demodulation,[],[f87,f92])).

fof(f87,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl4_2
    | spl4_3 ),
    inference(backward_demodulation,[],[f84,f78])).

fof(f84,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f86,plain,
    ( spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f81,f77,f83])).

fof(f81,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f62,f63])).

fof(f62,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f39,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f71,f77,f73])).

fof(f71,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(inner_rewriting,[],[f70])).

fof(f70,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f61,f63])).

fof(f61,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f40,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (31655)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (31638)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (31647)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (31639)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (31653)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (31639)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f80,f86,f113,f118,f134,f137,f143])).
% 0.22/0.56  fof(f143,plain,(
% 0.22/0.56    spl4_2 | ~spl4_7),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f142])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    $false | (spl4_2 | ~spl4_7)),
% 0.22/0.56    inference(subsumption_resolution,[],[f141,f79])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    sK0 != sK1 | spl4_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    spl4_2 <=> sK0 = sK1),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.56  fof(f141,plain,(
% 0.22/0.56    sK0 = sK1 | ~spl4_7),
% 0.22/0.56    inference(forward_demodulation,[],[f139,f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.56    inference(definition_unfolding,[],[f42,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f45,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.56  fof(f139,plain,(
% 0.22/0.56    sK1 = k3_subset_1(sK0,k1_xboole_0) | ~spl4_7),
% 0.22/0.56    inference(backward_demodulation,[],[f121,f133])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    k1_xboole_0 = k3_subset_1(sK0,sK1) | ~spl4_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f131])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    spl4_7 <=> k1_xboole_0 = k3_subset_1(sK0,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f38,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 0.22/0.56  % (31637)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.22/0.56    inference(negated_conjecture,[],[f15])).
% 0.22/0.56  fof(f15,conjecture,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.22/0.56  fof(f137,plain,(
% 0.22/0.56    spl4_6),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f136])).
% 0.22/0.56  fof(f136,plain,(
% 0.22/0.56    $false | spl4_6),
% 0.22/0.56    inference(subsumption_resolution,[],[f135,f38])).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_6),
% 0.22/0.56    inference(resolution,[],[f129,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl4_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f127])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    spl4_6 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    ~spl4_6 | spl4_7 | ~spl4_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f125,f83,f131,f127])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    spl4_3 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    k1_xboole_0 = k3_subset_1(sK0,sK1) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.22/0.56    inference(subsumption_resolution,[],[f123,f85])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl4_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f83])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | k1_xboole_0 = k3_subset_1(sK0,sK1) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(superposition,[],[f67,f121])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f55,f41])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.22/0.56  fof(f118,plain,(
% 0.22/0.56    spl4_1 | ~spl4_2),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f117])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    $false | (spl4_1 | ~spl4_2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f116,f111])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    r1_tarski(k1_xboole_0,sK0) | ~spl4_2),
% 0.22/0.56    inference(forward_demodulation,[],[f108,f63])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | ~spl4_2),
% 0.22/0.56    inference(resolution,[],[f107,f69])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.22/0.56    inference(equality_resolution,[],[f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f56,f41])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.22/0.56    inference(subsumption_resolution,[],[f96,f88])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.22/0.56    inference(backward_demodulation,[],[f38,f78])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    sK0 = sK1 | ~spl4_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f77])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.22/0.56    inference(superposition,[],[f52,f92])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    k1_xboole_0 = k3_subset_1(sK0,sK0) | ~spl4_2),
% 0.22/0.56    inference(forward_demodulation,[],[f91,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0) | ~spl4_2),
% 0.22/0.56    inference(forward_demodulation,[],[f90,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.56    inference(rectify,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) | ~spl4_2),
% 0.22/0.56    inference(resolution,[],[f88,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f53,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.56  fof(f116,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,sK0) | (spl4_1 | ~spl4_2)),
% 0.22/0.56    inference(forward_demodulation,[],[f75,f92])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl4_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    spl4_1 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    ~spl4_2 | spl4_3),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f112])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    $false | (~spl4_2 | spl4_3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f111,f94])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,sK0) | (~spl4_2 | spl4_3)),
% 0.22/0.56    inference(backward_demodulation,[],[f87,f92])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (~spl4_2 | spl4_3)),
% 0.22/0.56    inference(backward_demodulation,[],[f84,f78])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl4_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f83])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    spl4_3 | spl4_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f81,f77,f83])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f62,f63])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(definition_unfolding,[],[f39,f60])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ~spl4_1 | ~spl4_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f71,f77,f73])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.22/0.56    inference(inner_rewriting,[],[f70])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f61,f63])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(definition_unfolding,[],[f40,f60])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (31639)------------------------------
% 0.22/0.56  % (31639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (31639)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (31639)Memory used [KB]: 10746
% 0.22/0.56  % (31639)Time elapsed: 0.111 s
% 0.22/0.56  % (31639)------------------------------
% 0.22/0.56  % (31639)------------------------------
% 0.22/0.57  % (31630)Success in time 0.201 s
%------------------------------------------------------------------------------
