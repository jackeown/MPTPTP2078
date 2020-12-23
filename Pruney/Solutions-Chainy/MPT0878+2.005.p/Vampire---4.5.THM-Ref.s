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

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  48 expanded)
%              Number of leaves         :    3 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 142 expanded)
%              Number of equality atoms :   64 ( 141 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(subsumption_resolution,[],[f90,f13])).

fof(f13,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK0 != sK1
    & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) )
   => ( sK0 != sK1
      & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

fof(f90,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f89,f76])).

fof(f76,plain,(
    k1_xboole_0 != sK0 ),
    inference(superposition,[],[f13,f68])).

fof(f68,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f66,f13])).

fof(f66,plain,
    ( k1_xboole_0 = sK1
    | sK0 = sK1 ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X17,X15,X16] :
      ( k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X15,X16,X17)
      | k1_xboole_0 = sK1
      | sK1 = X15 ) ),
    inference(duplicate_literal_removal,[],[f32])).

fof(f32,plain,(
    ! [X17,X15,X16] :
      ( k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X15,X16,X17)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1
      | sK1 = X15 ) ),
    inference(superposition,[],[f18,f12])).

fof(f12,plain,(
    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f89,plain,
    ( k1_xboole_0 = sK0
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | sK0 = sK1 ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X17,X15,X16] :
      ( k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X15,X16,X17)
      | k1_xboole_0 = X17
      | k1_xboole_0 = X16
      | k1_xboole_0 = X15
      | sK1 = X15 ) ),
    inference(superposition,[],[f18,f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:48:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (9639)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  % (9639)Refutation not found, incomplete strategy% (9639)------------------------------
% 0.21/0.48  % (9639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9639)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9639)Memory used [KB]: 10490
% 0.21/0.48  % (9639)Time elapsed: 0.077 s
% 0.21/0.48  % (9639)------------------------------
% 0.21/0.48  % (9639)------------------------------
% 0.21/0.48  % (9655)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.49  % (9647)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (9655)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f90,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    sK0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    sK0 != sK1 & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : (X0 != X1 & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)) => (sK0 != sK1 & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ? [X0,X1] : (X0 != X1 & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.21/0.49    inference(negated_conjecture,[],[f3])).
% 0.21/0.49  fof(f3,conjecture,(
% 0.21/0.49    ! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    sK0 = sK1),
% 0.21/0.49    inference(subsumption_resolution,[],[f89,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(superposition,[],[f13,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    k1_xboole_0 = sK1),
% 0.21/0.49    inference(subsumption_resolution,[],[f66,f13])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = sK1),
% 0.21/0.49    inference(equality_resolution,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X17,X15,X16] : (k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X15,X16,X17) | k1_xboole_0 = sK1 | sK1 = X15) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X17,X15,X16] : (k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X15,X16,X17) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | sK1 = X15) )),
% 0.21/0.49    inference(superposition,[],[f18,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X3) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | sK0 = sK1),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK0 = sK1),
% 0.21/0.49    inference(equality_resolution,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X17,X15,X16] : (k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X15,X16,X17) | k1_xboole_0 = X17 | k1_xboole_0 = X16 | k1_xboole_0 = X15 | sK1 = X15) )),
% 0.21/0.49    inference(superposition,[],[f18,f12])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (9655)------------------------------
% 0.21/0.49  % (9655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9655)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (9655)Memory used [KB]: 1663
% 0.21/0.49  % (9655)Time elapsed: 0.096 s
% 0.21/0.49  % (9655)------------------------------
% 0.21/0.49  % (9655)------------------------------
% 0.21/0.50  % (9638)Success in time 0.132 s
%------------------------------------------------------------------------------
