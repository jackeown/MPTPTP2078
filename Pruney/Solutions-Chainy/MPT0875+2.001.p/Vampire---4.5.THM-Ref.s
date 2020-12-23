%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 160 expanded)
%              Number of leaves         :    4 (  33 expanded)
%              Depth                    :   23
%              Number of atoms          :  139 ( 706 expanded)
%              Number of equality atoms :  138 ( 705 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48,f25])).

fof(f25,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f48,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f47,f25])).

fof(f47,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2) ),
    inference(forward_demodulation,[],[f42,f38])).

fof(f38,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f37,f25])).

fof(f37,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f36,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f35])).

fof(f35,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f22,f33])).

fof(f33,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f32,f24])).

fof(f32,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f21,f29])).

fof(f29,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f28,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f17,f20])).

% (14784)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f20,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f15,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 )
    & ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
      | ( k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
          | ( k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) )
   => ( ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
      & ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
        | ( k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f21,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f13,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f41])).

% (14793)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f41,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f23,f38])).

fof(f23,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f12,f16])).

fof(f12,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:48:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (14788)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (14780)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (14803)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (14798)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (14785)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (14780)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (14787)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f48,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f47,f25])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f42,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    k1_xboole_0 = sK0),
% 0.22/0.53    inference(subsumption_resolution,[],[f37,f25])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) | k1_xboole_0 = sK0),
% 0.22/0.53    inference(forward_demodulation,[],[f36,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | k1_xboole_0 = sK0),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | k1_xboole_0 = sK0),
% 0.22/0.53    inference(superposition,[],[f22,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(subsumption_resolution,[],[f32,f24])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(superposition,[],[f21,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(subsumption_resolution,[],[f28,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(superposition,[],[f17,f20])).
% 0.22/0.53  % (14784)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(definition_unfolding,[],[f15,f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    (k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) & (k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) | (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))) => ((k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) & (k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) | (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)))),
% 0.22/0.53    inference(flattening,[],[f6])).
% 0.22/0.53  fof(f6,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <~> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.22/0.53    inference(negated_conjecture,[],[f3])).
% 0.22/0.53  fof(f3,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    k1_xboole_0 != sK2 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.22/0.53    inference(definition_unfolding,[],[f14,f16])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 != sK2),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.22/0.53    inference(definition_unfolding,[],[f13,f16])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f41])).
% 0.22/0.53  % (14793)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.22/0.53    inference(backward_demodulation,[],[f23,f38])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.22/0.53    inference(definition_unfolding,[],[f12,f16])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 != sK0),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (14780)------------------------------
% 0.22/0.53  % (14780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14780)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (14780)Memory used [KB]: 1663
% 0.22/0.53  % (14780)Time elapsed: 0.116 s
% 0.22/0.53  % (14780)------------------------------
% 0.22/0.53  % (14780)------------------------------
% 0.22/0.53  % (14797)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (14779)Success in time 0.165 s
%------------------------------------------------------------------------------
