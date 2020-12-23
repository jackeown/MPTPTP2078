%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 209 expanded)
%              Number of leaves         :    5 (  43 expanded)
%              Depth                    :   26
%              Number of atoms          :  208 (1088 expanded)
%              Number of equality atoms :  207 (1087 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(subsumption_resolution,[],[f66,f37])).

fof(f37,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f66,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f65,f35])).

fof(f35,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f65,plain,(
    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(k1_xboole_0,sK1,sK2),sK3) ),
    inference(forward_demodulation,[],[f61,f60])).

fof(f60,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f59,f37])).

fof(f59,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f58,f34])).

fof(f34,plain,(
    ! [X2,X0] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,k1_xboole_0,sK2),sK3)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,k1_xboole_0,sK2),sK3)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f31,f55])).

fof(f55,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f54,f37])).

fof(f54,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f53,f33])).

fof(f33,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,k1_xboole_0),sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f52])).

fof(f52,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,k1_xboole_0),sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f30,f50])).

fof(f50,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f49,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f27])).

% (17222)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f27,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f29,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f25,f28])).

fof(f28,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f19,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 )
    & ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | ( k1_xboole_0 != sK3
        & k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) )
   => ( ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
      & ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | ( k1_xboole_0 != sK3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f18,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f17,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f16,f20])).

fof(f16,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,(
    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(subsumption_resolution,[],[f32,f60])).

fof(f32,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f15,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 20:00:27 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.50  % (17214)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.50  % (17214)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f66,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)),
% 0.22/0.50    inference(forward_demodulation,[],[f65,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2,X1] : (k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(k1_xboole_0,sK1,sK2),sK3)),
% 0.22/0.50    inference(forward_demodulation,[],[f61,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f59,f37])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(forward_demodulation,[],[f58,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2,X0] : (k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,k1_xboole_0,sK2),sK3) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,k1_xboole_0,sK2),sK3) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(superposition,[],[f31,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f54,f37])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(forward_demodulation,[],[f53,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,k1_xboole_0),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,k1_xboole_0),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(superposition,[],[f30,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f49,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f27])).
% 0.22/0.50  % (17222)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),k1_xboole_0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(superposition,[],[f29,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(subsumption_resolution,[],[f45,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(superposition,[],[f25,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(definition_unfolding,[],[f19,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    (k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) & (k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | (k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : ((k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))) => ((k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) & (k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | (k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : ((k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)))),
% 0.22/0.50    inference(flattening,[],[f7])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : ((k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <~> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.22/0.50    inference(negated_conjecture,[],[f4])).
% 0.22/0.50  fof(f4,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    k1_xboole_0 != sK3 | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)),
% 0.22/0.50    inference(definition_unfolding,[],[f18,f20])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK3),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)),
% 0.22/0.50    inference(definition_unfolding,[],[f17,f20])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK2),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)),
% 0.22/0.50    inference(definition_unfolding,[],[f16,f20])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f32,f60])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)),
% 0.22/0.50    inference(definition_unfolding,[],[f15,f20])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK0),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (17214)------------------------------
% 0.22/0.50  % (17214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (17214)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (17214)Memory used [KB]: 6268
% 0.22/0.50  % (17214)Time elapsed: 0.098 s
% 0.22/0.50  % (17214)------------------------------
% 0.22/0.50  % (17214)------------------------------
% 0.22/0.51  % (17205)Success in time 0.145 s
%------------------------------------------------------------------------------
