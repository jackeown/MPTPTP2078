%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 104 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  164 ( 254 expanded)
%              Number of equality atoms :   49 (  89 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f44,f51,f57,f62,f68,f76,f108])).

fof(f108,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl3_1
    | spl3_2
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f106,f34])).

fof(f34,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f106,plain,
    ( k1_xboole_0 = sK1
    | spl3_1
    | spl3_2
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f105,f85])).

fof(f85,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_8 ),
    inference(resolution,[],[f61,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f61,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_8
  <=> v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f105,plain,
    ( sK1 = k2_relat_1(k1_xboole_0)
    | spl3_1
    | spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f104,f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK0
    | spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

% (1408)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f29,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f104,plain,
    ( sK1 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK0
    | spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f100,f34])).

fof(f100,plain,
    ( sK1 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_9 ),
    inference(superposition,[],[f27,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_9
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f76,plain,
    ( spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f74,f43])).

fof(f43,plain,
    ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_4
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f74,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f73,f23])).

fof(f23,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f73,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f47,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f47,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_5
  <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f53,f49,f66])).

fof(f49,plain,
    ( spl3_6
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f53,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f50,f24])).

fof(f50,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f62,plain,
    ( spl3_8
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f58,f55,f49,f60])).

fof(f55,plain,
    ( spl3_7
  <=> v1_xboole_0(k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f58,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f56,f53])).

fof(f56,plain,
    ( v1_xboole_0(k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f57,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f52,f49,f55])).

fof(f52,plain,
    ( v1_xboole_0(k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_6 ),
    inference(resolution,[],[f50,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

% (1397)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f51,plain,
    ( spl3_5
    | spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f37,f49,f46])).

fof(f37,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f40,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f38,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f38,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f44,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f39,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f29])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:21:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (1393)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (1387)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (1400)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (1387)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (1400)Refutation not found, incomplete strategy% (1400)------------------------------
% 0.20/0.53  % (1400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (1398)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.53  % (1391)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (1400)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (1400)Memory used [KB]: 6012
% 0.20/0.53  % (1400)Time elapsed: 0.004 s
% 0.20/0.53  % (1400)------------------------------
% 0.20/0.53  % (1400)------------------------------
% 0.20/0.53  % (1407)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.53  % (1398)Refutation not found, incomplete strategy% (1398)------------------------------
% 0.20/0.53  % (1398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (1398)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (1398)Memory used [KB]: 6140
% 0.20/0.53  % (1398)Time elapsed: 0.081 s
% 0.20/0.53  % (1398)------------------------------
% 0.20/0.53  % (1398)------------------------------
% 0.20/0.53  % (1404)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.53  % (1406)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f31,f35,f39,f44,f51,f57,f62,f68,f76,f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    spl3_1 | spl3_2 | ~spl3_8 | ~spl3_9),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    $false | (spl3_1 | spl3_2 | ~spl3_8 | ~spl3_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f106,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | spl3_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    spl3_2 <=> k1_xboole_0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | (spl3_1 | spl3_2 | ~spl3_8 | ~spl3_9)),
% 0.20/0.53    inference(forward_demodulation,[],[f105,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_8),
% 0.20/0.53    inference(resolution,[],[f61,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl3_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    spl3_8 <=> v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    sK1 = k2_relat_1(k1_xboole_0) | (spl3_1 | spl3_2 | ~spl3_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f104,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | spl3_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f29])).
% 0.20/0.53  % (1408)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    spl3_1 <=> k1_xboole_0 = sK0),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    sK1 = k2_relat_1(k1_xboole_0) | k1_xboole_0 = sK0 | (spl3_2 | ~spl3_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f100,f34])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    sK1 = k2_relat_1(k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl3_9),
% 0.20/0.53    inference(superposition,[],[f27,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    spl3_9 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    spl3_4 | ~spl3_5),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    $false | (spl3_4 | ~spl3_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f74,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | spl3_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    spl3_4 <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f73,f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_5),
% 0.20/0.53    inference(resolution,[],[f47,f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    spl3_5 <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    spl3_9 | ~spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f53,f49,f66])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    spl3_6 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_6),
% 0.20/0.53    inference(resolution,[],[f50,f24])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f49])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    spl3_8 | ~spl3_6 | ~spl3_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f58,f55,f49,f60])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    spl3_7 <=> v1_xboole_0(k2_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    v1_xboole_0(k2_relat_1(k1_xboole_0)) | (~spl3_6 | ~spl3_7)),
% 0.20/0.53    inference(forward_demodulation,[],[f56,f53])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    v1_xboole_0(k2_relat_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f55])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    spl3_7 | ~spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f52,f49,f55])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    v1_xboole_0(k2_relat_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_6),
% 0.20/0.53    inference(resolution,[],[f50,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.20/0.53  % (1397)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    spl3_5 | spl3_6 | ~spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f40,f37,f49,f46])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    spl3_3 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.20/0.53    inference(resolution,[],[f38,f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f37])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ~spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f18,f42])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.53    inference(negated_conjecture,[],[f7])).
% 0.20/0.53  fof(f7,conjecture,(
% 0.20/0.53    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f17,f37])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ~spl3_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f20,f33])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    k1_xboole_0 != sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ~spl3_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f19,f29])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    k1_xboole_0 != sK0),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (1387)------------------------------
% 0.20/0.53  % (1387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (1387)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (1387)Memory used [KB]: 6140
% 0.20/0.53  % (1387)Time elapsed: 0.082 s
% 0.20/0.53  % (1387)------------------------------
% 0.20/0.53  % (1387)------------------------------
% 0.20/0.53  % (1383)Success in time 0.174 s
%------------------------------------------------------------------------------
