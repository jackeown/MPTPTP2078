%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 414 expanded)
%              Number of leaves         :    6 ( 110 expanded)
%              Depth                    :   24
%              Number of atoms          :  124 (1172 expanded)
%              Number of equality atoms :  123 (1171 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f164,f176])).

fof(f176,plain,(
    ! [X6] : k1_xboole_0 = X6 ),
    inference(subsumption_resolution,[],[f173,f164])).

fof(f173,plain,(
    ! [X6] :
      ( k1_xboole_0 = X6
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f172,f33])).

fof(f33,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f21,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f30,plain,(
    ! [X2,X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f20,f17])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f172,plain,(
    ! [X6] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X6)
      | k1_xboole_0 = X6
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f167,f29])).

fof(f167,plain,(
    ! [X6] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0),X6)
      | k1_xboole_0 = X6
      | k1_xboole_0 = sK1 ) ),
    inference(backward_demodulation,[],[f66,f158])).

fof(f158,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(equality_factoring,[],[f149])).

fof(f149,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f148,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f18,f17])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f148,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ) ),
    inference(subsumption_resolution,[],[f144,f33])).

fof(f144,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f28,f129])).

fof(f129,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f127,f29])).

fof(f127,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f24,f124])).

fof(f124,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f123,f28])).

fof(f123,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f121,f14])).

fof(f14,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != sK1
    & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) )
   => ( sK0 != sK1
      & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f121,plain,
    ( sK0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(superposition,[],[f120,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f120,plain,
    ( sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f53,f28])).

fof(f53,plain,
    ( sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(superposition,[],[f16,f24])).

fof(f24,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(definition_unfolding,[],[f13,f23,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f22,f17])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f13,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X6] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0),X6)
      | k1_xboole_0 = X6
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f58,plain,(
    ! [X6] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0),X6)
      | k1_xboole_0 = X6
      | k1_xboole_0 = sK1
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ) ),
    inference(superposition,[],[f28,f24])).

fof(f164,plain,(
    k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f14,f158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n010.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:04:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (24029)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (24044)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (24026)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (24036)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (24033)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (24052)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (24033)Refutation not found, incomplete strategy% (24033)------------------------------
% 0.21/0.52  % (24033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24033)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24033)Memory used [KB]: 10618
% 0.21/0.52  % (24033)Time elapsed: 0.114 s
% 0.21/0.52  % (24033)------------------------------
% 0.21/0.52  % (24033)------------------------------
% 0.21/0.52  % (24028)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (24027)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (24044)Refutation not found, incomplete strategy% (24044)------------------------------
% 0.21/0.53  % (24044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24044)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24044)Memory used [KB]: 10618
% 0.21/0.53  % (24044)Time elapsed: 0.125 s
% 0.21/0.53  % (24044)------------------------------
% 0.21/0.53  % (24044)------------------------------
% 0.21/0.53  % (24047)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (24039)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (24039)Refutation not found, incomplete strategy% (24039)------------------------------
% 0.21/0.53  % (24039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24039)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24039)Memory used [KB]: 6140
% 0.21/0.53  % (24039)Time elapsed: 0.002 s
% 0.21/0.53  % (24039)------------------------------
% 0.21/0.53  % (24039)------------------------------
% 0.21/0.53  % (24031)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (24024)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (24024)Refutation not found, incomplete strategy% (24024)------------------------------
% 0.21/0.54  % (24024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24024)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24024)Memory used [KB]: 1663
% 0.21/0.54  % (24024)Time elapsed: 0.124 s
% 0.21/0.54  % (24024)------------------------------
% 0.21/0.54  % (24024)------------------------------
% 0.21/0.54  % (24051)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (24048)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (24053)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (24043)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (24053)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f201])).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0),
% 0.21/0.54    inference(superposition,[],[f164,f176])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ( ! [X6] : (k1_xboole_0 = X6) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f173,f164])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ( ! [X6] : (k1_xboole_0 = X6 | k1_xboole_0 = sK1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f172,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2)) )),
% 0.21/0.54    inference(superposition,[],[f30,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f21,f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.54    inference(nnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X2,X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f20,f17])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ( ! [X6] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X6) | k1_xboole_0 = X6 | k1_xboole_0 = sK1) )),
% 0.21/0.54    inference(forward_demodulation,[],[f167,f29])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    ( ! [X6] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0),X6) | k1_xboole_0 = X6 | k1_xboole_0 = sK1) )),
% 0.21/0.54    inference(backward_demodulation,[],[f66,f158])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    k1_xboole_0 = sK0),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f157])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(equality_factoring,[],[f149])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 = sK0 | k1_xboole_0 = X1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f148,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f18,f17])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 = X1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f144,f33])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f138])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = sK0) )),
% 0.21/0.54    inference(superposition,[],[f28,f129])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK0),
% 0.21/0.54    inference(forward_demodulation,[],[f127,f29])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.54    inference(superposition,[],[f24,f124])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f123,f28])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f121,f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    sK0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)) => (sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f7,plain,(
% 0.21/0.54    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.54    inference(negated_conjecture,[],[f5])).
% 0.21/0.54  fof(f5,conjecture,(
% 0.21/0.54    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    sK0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.54    inference(superposition,[],[f120,f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)) | k1_xboole_0 = sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f53,f28])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.21/0.54    inference(superposition,[],[f16,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 0.21/0.54    inference(definition_unfolding,[],[f13,f23,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f22,f17])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X6] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0),X6) | k1_xboole_0 = X6 | k1_xboole_0 = sK1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f58,f28])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X6] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0),X6) | k1_xboole_0 = X6 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)) )),
% 0.21/0.54    inference(superposition,[],[f28,f24])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    k1_xboole_0 != sK1),
% 0.21/0.54    inference(backward_demodulation,[],[f14,f158])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (24053)------------------------------
% 0.21/0.54  % (24053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24053)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (24053)Memory used [KB]: 1791
% 0.21/0.54  % (24053)Time elapsed: 0.143 s
% 0.21/0.54  % (24053)------------------------------
% 0.21/0.54  % (24053)------------------------------
% 0.21/0.54  % (24047)Refutation not found, incomplete strategy% (24047)------------------------------
% 0.21/0.54  % (24047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24047)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24047)Memory used [KB]: 1663
% 0.21/0.54  % (24047)Time elapsed: 0.101 s
% 0.21/0.54  % (24047)------------------------------
% 0.21/0.54  % (24047)------------------------------
% 0.21/0.54  % (24045)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (24040)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (24032)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (24035)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (24042)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (24030)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (24034)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (24023)Success in time 0.187 s
%------------------------------------------------------------------------------
