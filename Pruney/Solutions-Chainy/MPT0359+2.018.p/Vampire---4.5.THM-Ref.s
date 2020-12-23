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
% DateTime   : Thu Dec  3 12:44:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 257 expanded)
%              Number of leaves         :   15 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 ( 568 expanded)
%              Number of equality atoms :   37 ( 145 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f101,f126,f201,f333])).

fof(f333,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f243,f242,f240])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(sK0,sK0))
        | r2_hidden(X0,sK0) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f212,f70])).

fof(f70,plain,
    ( sK0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(sK0,sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f91,f70])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_xboole_0(sK1,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f57,f80])).

fof(f80,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f73,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f73,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f62,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f62,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f21,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f242,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,sK0),sK0),k5_xboole_0(sK0,sK0))
    | spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f83,f213])).

fof(f213,plain,
    ( k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f92,f70])).

fof(f92,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f61,f87])).

fof(f87,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f80,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f61,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f21,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f43])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f83,plain,
    ( r2_hidden(sK3(k3_subset_1(sK0,sK0),sK0),k3_subset_1(sK0,sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f67,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f67,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_1
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f243,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,sK0),sK0),sK0)
    | spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f84,f213])).

fof(f84,plain,
    ( ~ r2_hidden(sK3(k3_subset_1(sK0,sK0),sK0),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f67,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f201,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl5_3
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f100,f128,f144,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f144,plain,
    ( r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,sK1))
    | spl5_4 ),
    inference(forward_demodulation,[],[f141,f87])).

fof(f141,plain,
    ( r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f127,f128,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f127,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f125,f28])).

fof(f125,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f128,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f125,f29])).

fof(f100,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_3
  <=> r1_tarski(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f126,plain,
    ( ~ spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f94,f69,f123])).

fof(f94,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f87,f30])).

fof(f101,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f93,f98,f69])).

fof(f93,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f60,f92])).

fof(f60,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f19,f22])).

fof(f22,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f19,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f59,f69,f65])).

fof(f59,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(inner_rewriting,[],[f58])).

fof(f58,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f20,f22])).

fof(f20,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:42:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.49  % (2109)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.50  % (2103)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (2101)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (2104)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (2109)Refutation not found, incomplete strategy% (2109)------------------------------
% 0.19/0.51  % (2109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2109)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (2109)Memory used [KB]: 10618
% 0.19/0.51  % (2109)Time elapsed: 0.103 s
% 0.19/0.51  % (2109)------------------------------
% 0.19/0.51  % (2109)------------------------------
% 0.19/0.51  % (2125)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.51  % (2121)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (2117)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.51  % (2119)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.51  % (2121)Refutation not found, incomplete strategy% (2121)------------------------------
% 0.19/0.51  % (2121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2121)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (2121)Memory used [KB]: 10746
% 0.19/0.51  % (2121)Time elapsed: 0.085 s
% 0.19/0.51  % (2121)------------------------------
% 0.19/0.51  % (2121)------------------------------
% 0.19/0.52  % (2120)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.52  % (2127)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (2099)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (2100)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (2106)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.52  % (2112)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (2124)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.52  % (2105)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.53  % (2103)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f335,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(avatar_sat_refutation,[],[f72,f101,f126,f201,f333])).
% 0.19/0.53  fof(f333,plain,(
% 0.19/0.53    spl5_1 | ~spl5_2),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f325])).
% 0.19/0.53  fof(f325,plain,(
% 0.19/0.53    $false | (spl5_1 | ~spl5_2)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f243,f242,f240])).
% 0.19/0.53  fof(f240,plain,(
% 0.19/0.53    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK0,sK0)) | r2_hidden(X0,sK0)) ) | ~spl5_2),
% 0.19/0.53    inference(forward_demodulation,[],[f212,f70])).
% 0.19/0.53  fof(f70,plain,(
% 0.19/0.53    sK0 = sK1 | ~spl5_2),
% 0.19/0.53    inference(avatar_component_clause,[],[f69])).
% 0.19/0.53  fof(f69,plain,(
% 0.19/0.53    spl5_2 <=> sK0 = sK1),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.53  fof(f212,plain,(
% 0.19/0.53    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK0,sK0)) | r2_hidden(X0,sK1)) ) | ~spl5_2),
% 0.19/0.53    inference(backward_demodulation,[],[f91,f70])).
% 0.19/0.53  fof(f91,plain,(
% 0.19/0.53    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,sK1)) | r2_hidden(X0,sK1)) )),
% 0.19/0.53    inference(superposition,[],[f57,f80])).
% 0.19/0.53  fof(f80,plain,(
% 0.19/0.53    sK1 = k3_xboole_0(sK1,sK0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f73,f30])).
% 0.19/0.53  fof(f30,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f16])).
% 0.19/0.53  fof(f16,plain,(
% 0.19/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f6])).
% 0.19/0.53  fof(f6,axiom,(
% 0.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.53  fof(f73,plain,(
% 0.19/0.53    r1_tarski(sK1,sK0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f62,f53])).
% 0.19/0.53  fof(f53,plain,(
% 0.19/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.19/0.53    inference(equality_resolution,[],[f24])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f7])).
% 0.19/0.53  fof(f7,axiom,(
% 0.19/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.53  fof(f62,plain,(
% 0.19/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f36,f21,f35])).
% 0.19/0.53  fof(f35,plain,(
% 0.19/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f18])).
% 0.19/0.53  fof(f18,plain,(
% 0.19/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f8])).
% 0.19/0.53  fof(f8,axiom,(
% 0.19/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.53    inference(cnf_transformation,[],[f14])).
% 0.19/0.53  fof(f14,plain,(
% 0.19/0.53    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f13])).
% 0.19/0.53  fof(f13,negated_conjecture,(
% 0.19/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.19/0.53    inference(negated_conjecture,[],[f12])).
% 0.19/0.53  fof(f12,conjecture,(
% 0.19/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f11,axiom,(
% 0.19/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.19/0.53  fof(f57,plain,(
% 0.19/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 0.19/0.53    inference(equality_resolution,[],[f49])).
% 0.19/0.53  fof(f49,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.19/0.53    inference(definition_unfolding,[],[f40,f43])).
% 0.19/0.53  fof(f43,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f5])).
% 0.19/0.53  fof(f5,axiom,(
% 0.19/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.53  fof(f40,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.19/0.53    inference(cnf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.19/0.53  fof(f242,plain,(
% 0.19/0.53    r2_hidden(sK3(k5_xboole_0(sK0,sK0),sK0),k5_xboole_0(sK0,sK0)) | (spl5_1 | ~spl5_2)),
% 0.19/0.53    inference(backward_demodulation,[],[f83,f213])).
% 0.19/0.53  fof(f213,plain,(
% 0.19/0.53    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0) | ~spl5_2),
% 0.19/0.53    inference(backward_demodulation,[],[f92,f70])).
% 0.19/0.53  fof(f92,plain,(
% 0.19/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.19/0.53    inference(backward_demodulation,[],[f61,f87])).
% 0.19/0.53  fof(f87,plain,(
% 0.19/0.53    sK1 = k3_xboole_0(sK0,sK1)),
% 0.19/0.53    inference(superposition,[],[f80,f44])).
% 0.19/0.53  fof(f44,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.53  fof(f61,plain,(
% 0.19/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f21,f46])).
% 0.19/0.53  fof(f46,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.19/0.53    inference(definition_unfolding,[],[f31,f43])).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f17])).
% 0.19/0.53  fof(f17,plain,(
% 0.19/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f10])).
% 0.19/0.53  fof(f10,axiom,(
% 0.19/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.53  fof(f83,plain,(
% 0.19/0.53    r2_hidden(sK3(k3_subset_1(sK0,sK0),sK0),k3_subset_1(sK0,sK0)) | spl5_1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f67,f28])).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f15,plain,(
% 0.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f3])).
% 0.19/0.53  fof(f3,axiom,(
% 0.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.53  fof(f67,plain,(
% 0.19/0.53    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl5_1),
% 0.19/0.53    inference(avatar_component_clause,[],[f65])).
% 0.19/0.53  fof(f65,plain,(
% 0.19/0.53    spl5_1 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.53  fof(f243,plain,(
% 0.19/0.53    ~r2_hidden(sK3(k5_xboole_0(sK0,sK0),sK0),sK0) | (spl5_1 | ~spl5_2)),
% 0.19/0.53    inference(backward_demodulation,[],[f84,f213])).
% 0.19/0.53  fof(f84,plain,(
% 0.19/0.53    ~r2_hidden(sK3(k3_subset_1(sK0,sK0),sK0),sK0) | spl5_1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f67,f29])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f201,plain,(
% 0.19/0.53    ~spl5_3 | spl5_4),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f193])).
% 0.19/0.53  fof(f193,plain,(
% 0.19/0.53    $false | (~spl5_3 | spl5_4)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f100,f128,f144,f27])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f144,plain,(
% 0.19/0.53    r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,sK1)) | spl5_4),
% 0.19/0.53    inference(forward_demodulation,[],[f141,f87])).
% 0.19/0.53  fof(f141,plain,(
% 0.19/0.53    r2_hidden(sK3(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | spl5_4),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f127,f128,f55])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.19/0.53    inference(equality_resolution,[],[f47])).
% 0.19/0.53  fof(f47,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.19/0.53    inference(definition_unfolding,[],[f42,f43])).
% 0.19/0.53  fof(f42,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.19/0.53    inference(cnf_transformation,[],[f4])).
% 0.19/0.53  fof(f127,plain,(
% 0.19/0.53    r2_hidden(sK3(sK0,sK1),sK0) | spl5_4),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f125,f28])).
% 0.19/0.53  fof(f125,plain,(
% 0.19/0.53    ~r1_tarski(sK0,sK1) | spl5_4),
% 0.19/0.53    inference(avatar_component_clause,[],[f123])).
% 0.19/0.53  fof(f123,plain,(
% 0.19/0.53    spl5_4 <=> r1_tarski(sK0,sK1)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.53  fof(f128,plain,(
% 0.19/0.53    ~r2_hidden(sK3(sK0,sK1),sK1) | spl5_4),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f125,f29])).
% 0.19/0.53  fof(f100,plain,(
% 0.19/0.53    r1_tarski(k5_xboole_0(sK0,sK1),sK1) | ~spl5_3),
% 0.19/0.53    inference(avatar_component_clause,[],[f98])).
% 0.19/0.53  fof(f98,plain,(
% 0.19/0.53    spl5_3 <=> r1_tarski(k5_xboole_0(sK0,sK1),sK1)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.53  fof(f126,plain,(
% 0.19/0.53    ~spl5_4 | spl5_2),
% 0.19/0.53    inference(avatar_split_clause,[],[f94,f69,f123])).
% 0.19/0.53  fof(f94,plain,(
% 0.19/0.53    sK0 = sK1 | ~r1_tarski(sK0,sK1)),
% 0.19/0.53    inference(superposition,[],[f87,f30])).
% 0.19/0.53  fof(f101,plain,(
% 0.19/0.53    spl5_2 | spl5_3),
% 0.19/0.53    inference(avatar_split_clause,[],[f93,f98,f69])).
% 0.19/0.53  fof(f93,plain,(
% 0.19/0.53    r1_tarski(k5_xboole_0(sK0,sK1),sK1) | sK0 = sK1),
% 0.19/0.53    inference(backward_demodulation,[],[f60,f92])).
% 0.19/0.53  fof(f60,plain,(
% 0.19/0.53    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.19/0.53    inference(forward_demodulation,[],[f19,f22])).
% 0.19/0.53  fof(f22,plain,(
% 0.19/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f9])).
% 0.19/0.53  fof(f9,axiom,(
% 0.19/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.19/0.53  fof(f19,plain,(
% 0.19/0.53    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.19/0.53    inference(cnf_transformation,[],[f14])).
% 0.19/0.53  fof(f72,plain,(
% 0.19/0.53    ~spl5_1 | ~spl5_2),
% 0.19/0.53    inference(avatar_split_clause,[],[f59,f69,f65])).
% 0.19/0.53  fof(f59,plain,(
% 0.19/0.53    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.19/0.53    inference(inner_rewriting,[],[f58])).
% 0.19/0.53  fof(f58,plain,(
% 0.19/0.53    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.19/0.53    inference(forward_demodulation,[],[f20,f22])).
% 0.19/0.53  fof(f20,plain,(
% 0.19/0.53    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.19/0.53    inference(cnf_transformation,[],[f14])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (2103)------------------------------
% 0.19/0.53  % (2103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (2103)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (2103)Memory used [KB]: 6396
% 0.19/0.53  % (2103)Time elapsed: 0.132 s
% 0.19/0.53  % (2103)------------------------------
% 0.19/0.53  % (2103)------------------------------
% 0.19/0.53  % (2098)Success in time 0.177 s
%------------------------------------------------------------------------------
