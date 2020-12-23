%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   11 (  16 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  33 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f8,f9,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_finset_1)).

fof(f9,plain,(
    ~ v1_finset_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f6])).

fof(f6,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k3_xboole_0(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k3_xboole_0(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_finset_1)).

fof(f8,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (10677)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.46  % (10677)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f8,f9,f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_finset_1(k3_xboole_0(X0,X1)) | ~v1_finset_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ! [X0,X1] : (v1_finset_1(k3_xboole_0(X0,X1)) | ~v1_finset_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_finset_1)).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ~v1_finset_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ~v1_finset_1(k3_xboole_0(sK0,sK1)) & v1_finset_1(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1] : (~v1_finset_1(k3_xboole_0(X0,X1)) & v1_finset_1(X0)) => (~v1_finset_1(k3_xboole_0(sK0,sK1)) & v1_finset_1(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f4,plain,(
% 0.21/0.46    ? [X0,X1] : (~v1_finset_1(k3_xboole_0(X0,X1)) & v1_finset_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.21/0.46    inference(negated_conjecture,[],[f2])).
% 0.21/0.46  fof(f2,conjecture,(
% 0.21/0.46    ! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_finset_1)).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    v1_finset_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (10677)------------------------------
% 0.21/0.46  % (10677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (10677)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (10677)Memory used [KB]: 9722
% 0.21/0.46  % (10677)Time elapsed: 0.003 s
% 0.21/0.46  % (10677)------------------------------
% 0.21/0.46  % (10677)------------------------------
% 0.21/0.46  % (10664)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (10665)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (10658)Success in time 0.108 s
%------------------------------------------------------------------------------
