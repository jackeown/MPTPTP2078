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
% DateTime   : Thu Dec  3 12:59:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 530 expanded)
%              Number of leaves         :    6 ( 136 expanded)
%              Depth                    :   34
%              Number of atoms          :  138 (1404 expanded)
%              Number of equality atoms :  137 (1403 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(subsumption_resolution,[],[f137,f110])).

fof(f110,plain,(
    k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f14,f109])).

fof(f109,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f102,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f102,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f17,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f17,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f65,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f23,f63])).

fof(f63,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f54,f17])).

fof(f54,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f53])).

fof(f53,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f17,f47])).

fof(f47,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f46,f17])).

fof(f46,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(forward_demodulation,[],[f38,f25])).

fof(f25,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(superposition,[],[f23,f37])).

fof(f37,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f35,f14])).

fof(f35,plain,
    ( sK0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(superposition,[],[f32,f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f32,plain,
    ( sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(superposition,[],[f21,f23])).

fof(f23,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(definition_unfolding,[],[f13,f22,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f13,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f14,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f137,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f17,f130])).

fof(f130,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK1,sK1) ),
    inference(subsumption_resolution,[],[f127,f110])).

fof(f127,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f17,f122])).

fof(f122,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(subsumption_resolution,[],[f121,f110])).

fof(f121,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f114,f24])).

fof(f114,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f34,f109])).

fof(f34,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f17,f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:25:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (13807)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (13799)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (13799)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f137,f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(backward_demodulation,[],[f14,f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(superposition,[],[f17,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(superposition,[],[f17,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(forward_demodulation,[],[f65,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(superposition,[],[f23,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f54,f17])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.21/0.51    inference(superposition,[],[f17,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.21/0.51    inference(subsumption_resolution,[],[f46,f17])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f38,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.51    inference(superposition,[],[f23,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f35,f14])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    sK0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.51    inference(superposition,[],[f32,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.21/0.51    inference(superposition,[],[f21,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 0.21/0.51    inference(definition_unfolding,[],[f13,f22,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f15,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)) => (sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    sK0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    k1_xboole_0 = sK1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.51    inference(superposition,[],[f17,f130])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(sK1,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f110])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(superposition,[],[f17,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f121,f110])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(subsumption_resolution,[],[f114,f24])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(backward_demodulation,[],[f34,f109])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(superposition,[],[f17,f23])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (13799)------------------------------
% 0.21/0.51  % (13799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13799)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (13799)Memory used [KB]: 6268
% 0.21/0.51  % (13799)Time elapsed: 0.010 s
% 0.21/0.51  % (13799)------------------------------
% 0.21/0.51  % (13799)------------------------------
% 0.21/0.51  % (13793)Success in time 0.143 s
%------------------------------------------------------------------------------
