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
% DateTime   : Thu Dec  3 12:58:52 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 101 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :   19
%              Number of atoms          :  117 ( 267 expanded)
%              Number of equality atoms :  116 ( 266 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f156])).

fof(f156,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f128,f153])).

fof(f153,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f32,f136])).

fof(f136,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f129,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f129,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f28,f127])).

fof(f127,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f17,f111])).

fof(f111,plain,
    ( sK0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | sK0 = sK1 ),
    inference(superposition,[],[f25,f85])).

fof(f85,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = sK1 ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK1 = X1 ) ),
    inference(superposition,[],[f19,f28])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK0 != sK1
    & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) )
   => ( sK0 != sK1
      & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

fof(f28,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(definition_unfolding,[],[f16,f24,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f16,plain,(
    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f12])).

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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f128,plain,(
    k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f17,f127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:17:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.51  % (14209)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.51  % (14209)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.52  % (14207)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.52  % (14224)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.52  % (14206)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f157,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(trivial_inequality_removal,[],[f156])).
% 0.19/0.53  fof(f156,plain,(
% 0.19/0.53    k1_xboole_0 != k1_xboole_0),
% 0.19/0.53    inference(superposition,[],[f128,f153])).
% 0.19/0.53  fof(f153,plain,(
% 0.19/0.53    k1_xboole_0 = sK1),
% 0.19/0.53    inference(trivial_inequality_removal,[],[f152])).
% 0.19/0.53  fof(f152,plain,(
% 0.19/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 0.19/0.53    inference(duplicate_literal_removal,[],[f151])).
% 0.19/0.53  fof(f151,plain,(
% 0.19/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.19/0.53    inference(superposition,[],[f32,f136])).
% 0.19/0.53  fof(f136,plain,(
% 0.19/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.19/0.53    inference(forward_demodulation,[],[f129,f36])).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.53    inference(equality_resolution,[],[f27])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f15,plain,(
% 0.19/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.53    inference(flattening,[],[f14])).
% 0.19/0.53  fof(f14,plain,(
% 0.19/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.53    inference(nnf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.53  fof(f129,plain,(
% 0.19/0.53    k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.19/0.53    inference(backward_demodulation,[],[f28,f127])).
% 0.19/0.53  fof(f127,plain,(
% 0.19/0.53    k1_xboole_0 = sK0),
% 0.19/0.53    inference(trivial_inequality_removal,[],[f126])).
% 0.19/0.53  fof(f126,plain,(
% 0.19/0.53    sK0 != sK0 | k1_xboole_0 = sK0),
% 0.19/0.53    inference(superposition,[],[f17,f111])).
% 0.19/0.53  fof(f111,plain,(
% 0.19/0.53    sK0 = sK1 | k1_xboole_0 = sK0),
% 0.19/0.53    inference(trivial_inequality_removal,[],[f110])).
% 0.19/0.53  fof(f110,plain,(
% 0.19/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | sK0 = sK1),
% 0.19/0.53    inference(duplicate_literal_removal,[],[f101])).
% 0.19/0.53  fof(f101,plain,(
% 0.19/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK0 = sK1),
% 0.19/0.53    inference(superposition,[],[f25,f85])).
% 0.19/0.53  fof(f85,plain,(
% 0.19/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | k1_xboole_0 = sK0 | sK0 = sK1),
% 0.19/0.53    inference(equality_resolution,[],[f59])).
% 0.19/0.53  fof(f59,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK1 = X1) )),
% 0.19/0.53    inference(superposition,[],[f19,f28])).
% 0.19/0.53  fof(f19,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X3) )),
% 0.19/0.53    inference(cnf_transformation,[],[f9])).
% 0.19/0.53  fof(f9,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.19/0.53    inference(flattening,[],[f8])).
% 0.19/0.53  fof(f8,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.19/0.53    inference(ennf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f17,plain,(
% 0.19/0.53    sK0 != sK1),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f11,plain,(
% 0.19/0.53    sK0 != sK1 & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).
% 0.19/0.53  fof(f10,plain,(
% 0.19/0.53    ? [X0,X1] : (X0 != X1 & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)) => (sK0 != sK1 & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f7,plain,(
% 0.19/0.53    ? [X0,X1] : (X0 != X1 & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f6])).
% 0.19/0.53  fof(f6,negated_conjecture,(
% 0.19/0.53    ~! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.19/0.53    inference(negated_conjecture,[],[f5])).
% 0.19/0.53  fof(f5,conjecture,(
% 0.19/0.53    ! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.19/0.53    inference(definition_unfolding,[],[f16,f24,f24])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f3])).
% 0.19/0.53  fof(f3,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.19/0.53  fof(f16,plain,(
% 0.19/0.53    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f32,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(definition_unfolding,[],[f20,f24])).
% 0.19/0.53  fof(f20,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f13])).
% 0.19/0.53  fof(f13,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.53    inference(flattening,[],[f12])).
% 0.19/0.53  fof(f12,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.19/0.53    inference(nnf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.19/0.53  fof(f128,plain,(
% 0.19/0.53    k1_xboole_0 != sK1),
% 0.19/0.53    inference(backward_demodulation,[],[f17,f127])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (14209)------------------------------
% 0.19/0.53  % (14209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (14209)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (14209)Memory used [KB]: 1791
% 0.19/0.53  % (14209)Time elapsed: 0.111 s
% 0.19/0.53  % (14209)------------------------------
% 0.19/0.53  % (14209)------------------------------
% 0.19/0.53  % (14203)Success in time 0.181 s
%------------------------------------------------------------------------------
