%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  54 expanded)
%              Number of leaves         :    4 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 258 expanded)
%              Number of equality atoms :   48 ( 167 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f14])).

fof(f14,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k1_relat_1(sK1)
    & k1_xboole_0 = k1_relat_1(sK0)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f9,f8])).

fof(f8,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & k1_xboole_0 = k1_relat_1(X1)
            & k1_relat_1(X0) = k1_xboole_0
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(sK0)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X1] :
        ( sK0 != X1
        & k1_xboole_0 = k1_relat_1(X1)
        & k1_xboole_0 = k1_relat_1(sK0)
        & v1_relat_1(X1) )
   => ( sK0 != sK1
      & k1_xboole_0 = k1_relat_1(sK1)
      & k1_xboole_0 = k1_relat_1(sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_relat_1(X0) = k1_xboole_0
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_relat_1(X0) = k1_xboole_0
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k1_relat_1(X1)
                & k1_relat_1(X0) = k1_xboole_0 )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k1_relat_1(X1)
              & k1_relat_1(X0) = k1_xboole_0 )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_relat_1)).

fof(f26,plain,(
    k1_xboole_0 != k1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f24,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f15,f20])).

fof(f20,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f18,f13])).

fof(f13,plain,(
    k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relat_1(sK0) ),
    inference(resolution,[],[f11,f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK1) ),
    inference(resolution,[],[f12,f16])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (16773)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (16773)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f26,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    (sK0 != sK1 & k1_xboole_0 = k1_relat_1(sK1) & k1_xboole_0 = k1_relat_1(sK0) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f9,f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k1_relat_1(X1) & k1_relat_1(X0) = k1_xboole_0 & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (sK0 != X1 & k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(sK0) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X1] : (sK0 != X1 & k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(sK0) & v1_relat_1(X1)) => (sK0 != sK1 & k1_xboole_0 = k1_relat_1(sK1) & k1_xboole_0 = k1_relat_1(sK0) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f5,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k1_relat_1(X1) & k1_relat_1(X0) = k1_xboole_0 & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f4])).
% 0.20/0.47  fof(f4,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((X0 != X1 & (k1_xboole_0 = k1_relat_1(X1) & k1_relat_1(X0) = k1_xboole_0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_relat_1(X0) = k1_xboole_0) => X0 = X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f2])).
% 0.20/0.47  fof(f2,conjecture,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_relat_1(X0) = k1_xboole_0) => X0 = X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_relat_1)).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    k1_xboole_0 != k1_relat_1(sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f24,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    k1_xboole_0 != sK1),
% 0.20/0.47    inference(backward_demodulation,[],[f15,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    k1_xboole_0 = sK0),
% 0.20/0.47    inference(subsumption_resolution,[],[f18,f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relat_1(sK0)),
% 0.20/0.47    inference(resolution,[],[f11,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    sK0 != sK1),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK1)),
% 0.20/0.47    inference(resolution,[],[f12,f16])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (16773)------------------------------
% 0.20/0.47  % (16773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16773)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (16773)Memory used [KB]: 1535
% 0.20/0.47  % (16773)Time elapsed: 0.028 s
% 0.20/0.47  % (16773)------------------------------
% 0.20/0.47  % (16773)------------------------------
% 0.20/0.47  % (16768)Success in time 0.114 s
%------------------------------------------------------------------------------
