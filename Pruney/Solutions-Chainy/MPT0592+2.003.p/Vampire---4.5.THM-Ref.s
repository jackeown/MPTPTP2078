%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  57 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 ( 181 expanded)
%              Number of equality atoms :   30 ( 108 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,plain,(
    $false ),
    inference(subsumption_resolution,[],[f27,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f12,f19])).

fof(f19,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f18,f17])).

fof(f17,plain,(
    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f9,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f9,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k1_relat_1(X1)
                & k1_xboole_0 = k1_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k1_relat_1(X1)
              & k1_xboole_0 = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_relat_1)).

fof(f18,plain,(
    sK1 = k7_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f16,f11])).

fof(f11,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,plain,(
    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f9,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f12,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f6])).

fof(f27,plain,(
    k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f26,f25])).

fof(f25,plain,(
    k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f13,f14])).

fof(f13,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f26,plain,(
    sK0 = k7_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f24,f10])).

fof(f10,plain,(
    k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f24,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f13,f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:44:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (22124)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.42  % (22124)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f27,f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    k1_xboole_0 != sK0),
% 0.20/0.42    inference(backward_demodulation,[],[f12,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    k1_xboole_0 = sK1),
% 0.20/0.42    inference(backward_demodulation,[],[f18,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)),
% 0.20/0.42    inference(resolution,[],[f9,f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    v1_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f5])).
% 0.20/0.42  fof(f5,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((X0 != X1 & (k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0)) => X0 = X1)))),
% 0.20/0.42    inference(negated_conjecture,[],[f3])).
% 0.20/0.42  fof(f3,conjecture,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0)) => X0 = X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_relat_1)).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    sK1 = k7_relat_1(sK1,k1_xboole_0)),
% 0.20/0.42    inference(forward_demodulation,[],[f16,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    k1_xboole_0 = k1_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    sK1 = k7_relat_1(sK1,k1_relat_1(sK1))),
% 0.20/0.42    inference(resolution,[],[f9,f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    sK0 != sK1),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    k1_xboole_0 = sK0),
% 0.20/0.42    inference(backward_demodulation,[],[f26,f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)),
% 0.20/0.42    inference(resolution,[],[f13,f14])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    v1_relat_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    sK0 = k7_relat_1(sK0,k1_xboole_0)),
% 0.20/0.42    inference(forward_demodulation,[],[f24,f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.42    inference(resolution,[],[f13,f15])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (22124)------------------------------
% 0.20/0.42  % (22124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (22124)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (22124)Memory used [KB]: 1535
% 0.20/0.42  % (22124)Time elapsed: 0.004 s
% 0.20/0.42  % (22124)------------------------------
% 0.20/0.42  % (22124)------------------------------
% 0.20/0.43  % (22110)Success in time 0.063 s
%------------------------------------------------------------------------------
