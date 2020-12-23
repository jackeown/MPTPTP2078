%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   23 (  51 expanded)
%              Number of leaves         :    3 (  10 expanded)
%              Depth                    :   12
%              Number of atoms          :   57 ( 123 expanded)
%              Number of equality atoms :   56 ( 122 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(subsumption_resolution,[],[f58,f48])).

fof(f48,plain,(
    k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f9,f47])).

fof(f47,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f46])).

fof(f46,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f13,f34])).

fof(f34,plain,(
    k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f8,f33])).

fof(f33,plain,(
    k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f32,f9])).

fof(f32,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK0,sK0)
      | k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0)
      | sK1 = X0 ) ),
    inference(superposition,[],[f10,f8])).

fof(f10,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f8,plain,(
    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_mcart_1)).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f9,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f5])).

fof(f58,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f57])).

% (28244)Refutation not found, incomplete strategy% (28244)------------------------------
% (28244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f57,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f13,f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:36:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (28239)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (28248)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (28238)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (28238)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (28235)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (28251)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (28237)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (28247)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (28258)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (28236)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (28246)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (28256)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (28249)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (28245)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (28233)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (28243)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (28233)Refutation not found, incomplete strategy% (28233)------------------------------
% 0.22/0.52  % (28233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28233)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28233)Memory used [KB]: 10490
% 0.22/0.52  % (28233)Time elapsed: 0.101 s
% 0.22/0.52  % (28233)------------------------------
% 0.22/0.52  % (28233)------------------------------
% 0.22/0.52  % (28254)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (28234)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (28244)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f58,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    k1_xboole_0 != sK0),
% 0.22/0.52    inference(backward_demodulation,[],[f9,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    k1_xboole_0 = sK1),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f13,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.22/0.52    inference(backward_demodulation,[],[f8,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f32,f9])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0) | sK0 = sK1),
% 0.22/0.52    inference(equality_resolution,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK0,sK0) | k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0) | sK1 = X0) )),
% 0.22/0.52    inference(superposition,[],[f10,f8])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | X0 = X3) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.22/0.52    inference(flattening,[],[f6])).
% 0.22/0.52  fof(f6,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,plain,(
% 0.22/0.52    ? [X0,X1] : (X0 != X1 & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.22/0.52    inference(negated_conjecture,[],[f3])).
% 0.22/0.52  fof(f3,conjecture,(
% 0.22/0.52    ! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_mcart_1)).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    sK0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    k1_xboole_0 = sK0),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f57])).
% 0.22/0.52  % (28244)Refutation not found, incomplete strategy% (28244)------------------------------
% 0.22/0.52  % (28244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.22/0.52    inference(superposition,[],[f13,f33])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (28238)------------------------------
% 0.22/0.52  % (28238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28238)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (28238)Memory used [KB]: 6140
% 0.22/0.52  % (28238)Time elapsed: 0.085 s
% 0.22/0.52  % (28238)------------------------------
% 0.22/0.52  % (28238)------------------------------
% 0.22/0.52  % (28232)Success in time 0.154 s
%------------------------------------------------------------------------------
