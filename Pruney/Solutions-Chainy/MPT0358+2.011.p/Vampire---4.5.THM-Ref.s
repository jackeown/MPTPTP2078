%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  98 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 222 expanded)
%              Number of equality atoms :   29 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f318,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f249,f317])).

fof(f317,plain,
    ( spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f304,f51])).

fof(f51,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f304,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_3 ),
    inference(resolution,[],[f271,f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f271,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f263,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f263,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k4_xboole_0(sK0,sK1)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f259,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f259,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f56,f59])).

fof(f59,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f18,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

% (32241)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f56,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_3
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f249,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f39,f236])).

fof(f236,plain,
    ( ! [X6] : ~ r1_tarski(X6,k1_xboole_0)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f235,f76])).

fof(f76,plain,
    ( r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)),k1_xboole_0)
    | spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f66,f60])).

fof(f60,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f58,f50])).

fof(f50,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f58,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f18,f23])).

fof(f66,plain,
    ( r2_hidden(sK4(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)),k1_xboole_0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f47,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_1
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f235,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)),k1_xboole_0)
        | ~ r1_tarski(X6,k1_xboole_0) )
    | spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f155,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f155,plain,
    ( ! [X0] : ~ r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)),k4_xboole_0(X0,k1_xboole_0))
    | spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f76,f41])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f57,plain,
    ( spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f37,f49,f54])).

fof(f37,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f16,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f43,f49,f45])).

fof(f43,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f36])).

fof(f36,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f17,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (32244)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (32239)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (32252)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (32260)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (32254)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (32242)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (32246)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (32246)Refutation not found, incomplete strategy% (32246)------------------------------
% 0.21/0.52  % (32246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32246)Memory used [KB]: 10618
% 0.21/0.52  % (32246)Time elapsed: 0.108 s
% 0.21/0.52  % (32246)------------------------------
% 0.21/0.52  % (32246)------------------------------
% 0.21/0.52  % (32236)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (32256)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (32262)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (32240)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (32237)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (32264)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (32247)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (32235)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (32237)Refutation not found, incomplete strategy% (32237)------------------------------
% 0.21/0.53  % (32237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32237)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32237)Memory used [KB]: 10618
% 0.21/0.53  % (32237)Time elapsed: 0.124 s
% 0.21/0.53  % (32237)------------------------------
% 0.21/0.53  % (32237)------------------------------
% 0.21/0.53  % (32258)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (32244)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f52,f57,f249,f317])).
% 0.21/0.54  fof(f317,plain,(
% 0.21/0.54    spl5_2 | ~spl5_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f316])).
% 0.21/0.54  fof(f316,plain,(
% 0.21/0.54    $false | (spl5_2 | ~spl5_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f304,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | spl5_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    spl5_2 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.54  fof(f304,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f271,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl5_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f263,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.54  fof(f263,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,k4_xboole_0(sK0,sK1))) ) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f259,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | ~spl5_3),
% 0.21/0.54    inference(forward_demodulation,[],[f56,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f18,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  % (32241)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl5_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    spl5_3 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    spl5_1 | ~spl5_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f237])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    $false | (spl5_1 | ~spl5_2)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f39,f236])).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    ( ! [X6] : (~r1_tarski(X6,k1_xboole_0)) ) | (spl5_1 | ~spl5_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f235,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)),k1_xboole_0) | (spl5_1 | ~spl5_2)),
% 0.21/0.54    inference(forward_demodulation,[],[f66,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    k3_subset_1(sK0,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0) | ~spl5_2),
% 0.21/0.54    inference(forward_demodulation,[],[f58,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl5_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f49])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f18,f23])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    r2_hidden(sK4(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)),k1_xboole_0) | spl5_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f47,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | spl5_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    spl5_1 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    ( ! [X6] : (~r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)),k1_xboole_0) | ~r1_tarski(X6,k1_xboole_0)) ) | (spl5_1 | ~spl5_2)),
% 0.21/0.54    inference(superposition,[],[f155,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK4(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)),k4_xboole_0(X0,k1_xboole_0))) ) | (spl5_1 | ~spl5_2)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f76,f41])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    spl5_3 | spl5_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f37,f49,f54])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.54    inference(definition_unfolding,[],[f16,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ~spl5_1 | ~spl5_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f49,f45])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.21/0.54    inference(inner_rewriting,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.54    inference(definition_unfolding,[],[f17,f19])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (32244)------------------------------
% 0.21/0.54  % (32244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32244)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (32244)Memory used [KB]: 10746
% 0.21/0.54  % (32244)Time elapsed: 0.131 s
% 0.21/0.54  % (32244)------------------------------
% 0.21/0.54  % (32244)------------------------------
% 0.21/0.54  % (32245)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (32238)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (32234)Success in time 0.178 s
%------------------------------------------------------------------------------
