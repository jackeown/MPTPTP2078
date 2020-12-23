%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 138 expanded)
%              Number of leaves         :    7 (  35 expanded)
%              Depth                    :   21
%              Number of atoms          :  137 ( 363 expanded)
%              Number of equality atoms :  136 ( 362 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f110,f133])).

fof(f133,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f132])).

fof(f132,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f27,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) ),
    inference(forward_demodulation,[],[f122,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f122,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) ),
    inference(forward_demodulation,[],[f115,f39])).

fof(f115,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) ),
    inference(backward_demodulation,[],[f77,f108])).

fof(f108,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f107])).

fof(f107,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f18,f91])).

fof(f91,plain,
    ( sK0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | sK0 = sK1 ),
    inference(superposition,[],[f35,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK0
    | sK0 = sK1 ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK1 = X1 ) ),
    inference(superposition,[],[f20,f31])).

fof(f31,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(definition_unfolding,[],[f17,f30,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f17,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK0 != sK1
    & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) )
   => ( sK0 != sK1
      & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f22,f26])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f13])).

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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) ),
    inference(superposition,[],[f35,f31])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f110,plain,(
    k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f18,f108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:29:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.49  % (6424)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.49  % (6424)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f137,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f136])).
% 0.19/0.49  fof(f136,plain,(
% 0.19/0.49    k1_xboole_0 != k1_xboole_0),
% 0.19/0.49    inference(superposition,[],[f110,f133])).
% 0.19/0.49  fof(f133,plain,(
% 0.19/0.49    k1_xboole_0 = sK1),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f132])).
% 0.19/0.49  fof(f132,plain,(
% 0.19/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f129])).
% 0.19/0.49  fof(f129,plain,(
% 0.19/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.19/0.49    inference(superposition,[],[f27,f124])).
% 0.19/0.49  fof(f124,plain,(
% 0.19/0.49    k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | k1_xboole_0 = sK1),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f123])).
% 0.19/0.49  fof(f123,plain,(
% 0.19/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)),
% 0.19/0.49    inference(forward_demodulation,[],[f122,f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.49    inference(flattening,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.49    inference(nnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.49  fof(f122,plain,(
% 0.19/0.49    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)),
% 0.19/0.49    inference(forward_demodulation,[],[f115,f39])).
% 0.19/0.49  fof(f115,plain,(
% 0.19/0.49    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)),
% 0.19/0.49    inference(backward_demodulation,[],[f77,f108])).
% 0.19/0.49  fof(f108,plain,(
% 0.19/0.49    k1_xboole_0 = sK0),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f107])).
% 0.19/0.49  fof(f107,plain,(
% 0.19/0.49    sK0 != sK0 | k1_xboole_0 = sK0),
% 0.19/0.49    inference(superposition,[],[f18,f91])).
% 0.19/0.49  fof(f91,plain,(
% 0.19/0.49    sK0 = sK1 | k1_xboole_0 = sK0),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f90])).
% 0.19/0.49  fof(f90,plain,(
% 0.19/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | sK0 = sK1),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f89])).
% 0.19/0.49  fof(f89,plain,(
% 0.19/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK0 = sK1),
% 0.19/0.49    inference(superposition,[],[f35,f71])).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = sK0 | sK0 = sK1),
% 0.19/0.49    inference(equality_resolution,[],[f62])).
% 0.19/0.49  fof(f62,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK1 = X1) )),
% 0.19/0.49    inference(superposition,[],[f20,f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 0.19/0.49    inference(definition_unfolding,[],[f17,f30,f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f21,f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)) => (sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f8,plain,(
% 0.19/0.49    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.19/0.49    inference(negated_conjecture,[],[f6])).
% 0.19/0.49  fof(f6,conjecture,(
% 0.19/0.49    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X3) )),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.19/0.49    inference(flattening,[],[f9])).
% 0.19/0.49  fof(f9,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.49    inference(definition_unfolding,[],[f22,f26])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.49    inference(flattening,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.19/0.49    inference(nnf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    sK0 != sK1),
% 0.19/0.49    inference(cnf_transformation,[],[f12])).
% 0.19/0.49  fof(f77,plain,(
% 0.19/0.49    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f75])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)),
% 0.19/0.49    inference(superposition,[],[f35,f31])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f110,plain,(
% 0.19/0.49    k1_xboole_0 != sK1),
% 0.19/0.49    inference(backward_demodulation,[],[f18,f108])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (6424)------------------------------
% 0.19/0.49  % (6424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (6424)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (6424)Memory used [KB]: 1791
% 0.19/0.49  % (6424)Time elapsed: 0.102 s
% 0.19/0.49  % (6424)------------------------------
% 0.19/0.49  % (6424)------------------------------
% 0.19/0.49  % (6418)Success in time 0.146 s
%------------------------------------------------------------------------------
