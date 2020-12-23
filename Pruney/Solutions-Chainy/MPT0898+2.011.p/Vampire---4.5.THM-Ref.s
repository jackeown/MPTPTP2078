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
% DateTime   : Thu Dec  3 12:59:16 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 729 expanded)
%              Number of leaves         :    6 ( 210 expanded)
%              Depth                    :   16
%              Number of atoms          :  129 (1808 expanded)
%              Number of equality atoms :  128 (1807 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f416,f416,f416,f416,f422,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f18,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f422,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) ),
    inference(forward_demodulation,[],[f417,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f22,f26])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f417,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f27,f386])).

fof(f386,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f385,f82])).

fof(f82,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f32,f27])).

fof(f385,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f384,f44])).

fof(f44,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(superposition,[],[f37,f36])).

fof(f37,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f384,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f364,f44])).

fof(f364,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f27,f320])).

fof(f320,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f309,f15])).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK0 != sK1
    & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
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

fof(f309,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | sK0 = sK1 ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X26,X24,X25] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) != k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
      | sK1 = X26 ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X26,X24,X25] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) != k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
      | sK1 = X26 ) ),
    inference(superposition,[],[f33,f27])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f25,f16,f16])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f27,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(definition_unfolding,[],[f14,f26,f26])).

fof(f14,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f416,plain,(
    k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f15,f386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (15649)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (15675)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (15647)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.24/0.52  % (15658)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.24/0.52  % (15658)Refutation not found, incomplete strategy% (15658)------------------------------
% 1.24/0.52  % (15658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (15646)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.52  % (15645)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.52  % (15646)Refutation not found, incomplete strategy% (15646)------------------------------
% 1.24/0.52  % (15646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (15646)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (15646)Memory used [KB]: 1663
% 1.24/0.52  % (15646)Time elapsed: 0.116 s
% 1.24/0.52  % (15646)------------------------------
% 1.24/0.52  % (15646)------------------------------
% 1.24/0.52  % (15658)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (15658)Memory used [KB]: 10618
% 1.24/0.52  % (15658)Time elapsed: 0.116 s
% 1.24/0.52  % (15658)------------------------------
% 1.24/0.52  % (15658)------------------------------
% 1.24/0.53  % (15650)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.53  % (15669)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.24/0.53  % (15649)Refutation found. Thanks to Tanya!
% 1.24/0.53  % SZS status Theorem for theBenchmark
% 1.24/0.53  % SZS output start Proof for theBenchmark
% 1.24/0.53  fof(f474,plain,(
% 1.24/0.53    $false),
% 1.24/0.53    inference(unit_resulting_resolution,[],[f416,f416,f416,f416,f422,f32])).
% 1.24/0.53  fof(f32,plain,(
% 1.24/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.24/0.53    inference(definition_unfolding,[],[f18,f26])).
% 1.24/0.53  fof(f26,plain,(
% 1.24/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.24/0.53    inference(definition_unfolding,[],[f17,f16])).
% 1.24/0.53  fof(f16,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f1])).
% 1.24/0.53  fof(f1,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.24/0.53  fof(f17,plain,(
% 1.24/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f2])).
% 1.24/0.53  fof(f2,axiom,(
% 1.24/0.53    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.24/0.53  fof(f18,plain,(
% 1.24/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f13])).
% 1.24/0.53  fof(f13,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.24/0.53    inference(flattening,[],[f12])).
% 1.24/0.53  fof(f12,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.24/0.53    inference(nnf_transformation,[],[f4])).
% 1.24/0.53  fof(f4,axiom,(
% 1.24/0.53    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.24/0.53  fof(f422,plain,(
% 1.24/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)),
% 1.24/0.53    inference(forward_demodulation,[],[f417,f36])).
% 1.24/0.53  fof(f36,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 1.24/0.53    inference(equality_resolution,[],[f28])).
% 1.24/0.53  fof(f28,plain,(
% 1.24/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.24/0.53    inference(definition_unfolding,[],[f22,f26])).
% 1.24/0.53  fof(f22,plain,(
% 1.24/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f13])).
% 1.24/0.53  fof(f417,plain,(
% 1.24/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)),
% 1.24/0.53    inference(backward_demodulation,[],[f27,f386])).
% 1.24/0.53  fof(f386,plain,(
% 1.24/0.53    k1_xboole_0 = sK1),
% 1.24/0.53    inference(subsumption_resolution,[],[f385,f82])).
% 1.24/0.53  fof(f82,plain,(
% 1.24/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1),
% 1.24/0.53    inference(duplicate_literal_removal,[],[f81])).
% 1.24/0.53  fof(f81,plain,(
% 1.24/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.24/0.53    inference(superposition,[],[f32,f27])).
% 1.24/0.53  fof(f385,plain,(
% 1.24/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1),
% 1.24/0.53    inference(forward_demodulation,[],[f384,f44])).
% 1.24/0.53  fof(f44,plain,(
% 1.24/0.53    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 1.24/0.53    inference(superposition,[],[f37,f36])).
% 1.24/0.53  fof(f37,plain,(
% 1.24/0.53    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 1.24/0.53    inference(equality_resolution,[],[f29])).
% 1.24/0.53  fof(f29,plain,(
% 1.24/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.24/0.53    inference(definition_unfolding,[],[f21,f26])).
% 1.24/0.53  fof(f21,plain,(
% 1.24/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f13])).
% 1.24/0.53  fof(f384,plain,(
% 1.24/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 = sK1),
% 1.24/0.53    inference(forward_demodulation,[],[f364,f44])).
% 1.24/0.53  fof(f364,plain,(
% 1.24/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK1) | k1_xboole_0 = sK1),
% 1.24/0.53    inference(superposition,[],[f27,f320])).
% 1.24/0.53  fof(f320,plain,(
% 1.24/0.53    k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | k1_xboole_0 = sK1),
% 1.24/0.53    inference(subsumption_resolution,[],[f309,f15])).
% 1.24/0.53  fof(f15,plain,(
% 1.24/0.53    sK0 != sK1),
% 1.24/0.53    inference(cnf_transformation,[],[f11])).
% 1.24/0.53  fof(f11,plain,(
% 1.24/0.53    sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).
% 1.24/0.53  fof(f10,plain,(
% 1.24/0.53    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)) => (sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f7,plain,(
% 1.24/0.53    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 1.24/0.53    inference(ennf_transformation,[],[f6])).
% 1.24/0.53  fof(f6,negated_conjecture,(
% 1.24/0.53    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 1.24/0.53    inference(negated_conjecture,[],[f5])).
% 1.24/0.53  fof(f5,conjecture,(
% 1.24/0.53    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).
% 1.24/0.53  fof(f309,plain,(
% 1.24/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | sK0 = sK1),
% 1.24/0.53    inference(equality_resolution,[],[f116])).
% 1.24/0.53  fof(f116,plain,(
% 1.24/0.53    ( ! [X26,X24,X25] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) != k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | sK1 = X26) )),
% 1.24/0.53    inference(duplicate_literal_removal,[],[f100])).
% 1.24/0.53  fof(f100,plain,(
% 1.24/0.53    ( ! [X26,X24,X25] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) != k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | sK1 = X26) )),
% 1.24/0.53    inference(superposition,[],[f33,f27])).
% 1.24/0.53  fof(f33,plain,(
% 1.24/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X2 = X5) )),
% 1.24/0.53    inference(definition_unfolding,[],[f25,f16,f16])).
% 1.24/0.53  fof(f25,plain,(
% 1.24/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f9])).
% 1.24/0.53  fof(f9,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.24/0.53    inference(flattening,[],[f8])).
% 1.24/0.53  fof(f8,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.24/0.53    inference(ennf_transformation,[],[f3])).
% 1.24/0.53  fof(f3,axiom,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).
% 1.24/0.53  fof(f27,plain,(
% 1.24/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 1.24/0.53    inference(definition_unfolding,[],[f14,f26,f26])).
% 1.24/0.53  fof(f14,plain,(
% 1.24/0.53    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 1.24/0.53    inference(cnf_transformation,[],[f11])).
% 1.24/0.53  fof(f416,plain,(
% 1.24/0.53    k1_xboole_0 != sK0),
% 1.24/0.53    inference(backward_demodulation,[],[f15,f386])).
% 1.24/0.53  % SZS output end Proof for theBenchmark
% 1.24/0.53  % (15649)------------------------------
% 1.24/0.53  % (15649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (15649)Termination reason: Refutation
% 1.24/0.53  
% 1.24/0.53  % (15649)Memory used [KB]: 1918
% 1.24/0.53  % (15649)Time elapsed: 0.115 s
% 1.24/0.53  % (15649)------------------------------
% 1.24/0.53  % (15649)------------------------------
% 1.38/0.53  % (15641)Success in time 0.173 s
%------------------------------------------------------------------------------
