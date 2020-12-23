%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   15 (  27 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  80 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f12])).

fof(f12,plain,(
    ~ v1_finset_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ v1_finset_1(k2_xboole_0(sK0,sK1))
    & v1_finset_1(sK1)
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k2_xboole_0(X0,X1))
        & v1_finset_1(X1)
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k2_xboole_0(sK0,sK1))
      & v1_finset_1(sK1)
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k2_xboole_0(X0,X1))
      & v1_finset_1(X1)
      & v1_finset_1(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k2_xboole_0(X0,X1))
      & v1_finset_1(X1)
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_finset_1(X1)
          & v1_finset_1(X0) )
       => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_finset_1)).

fof(f18,plain,(
    v1_finset_1(k2_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f10,f11,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_finset_1)).

fof(f11,plain,(
    v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (2640)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.22/0.45  % (2640)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(subsumption_resolution,[],[f18,f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ~v1_finset_1(k2_xboole_0(sK0,sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ~v1_finset_1(k2_xboole_0(sK0,sK1)) & v1_finset_1(sK1) & v1_finset_1(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0,X1] : (~v1_finset_1(k2_xboole_0(X0,X1)) & v1_finset_1(X1) & v1_finset_1(X0)) => (~v1_finset_1(k2_xboole_0(sK0,sK1)) & v1_finset_1(sK1) & v1_finset_1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f5,plain,(
% 0.22/0.45    ? [X0,X1] : (~v1_finset_1(k2_xboole_0(X0,X1)) & v1_finset_1(X1) & v1_finset_1(X0))),
% 0.22/0.45    inference(flattening,[],[f4])).
% 0.22/0.45  fof(f4,plain,(
% 0.22/0.45    ? [X0,X1] : (~v1_finset_1(k2_xboole_0(X0,X1)) & (v1_finset_1(X1) & v1_finset_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1] : ((v1_finset_1(X1) & v1_finset_1(X0)) => v1_finset_1(k2_xboole_0(X0,X1)))),
% 0.22/0.45    inference(negated_conjecture,[],[f2])).
% 0.22/0.45  fof(f2,conjecture,(
% 0.22/0.45    ! [X0,X1] : ((v1_finset_1(X1) & v1_finset_1(X0)) => v1_finset_1(k2_xboole_0(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_finset_1)).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    v1_finset_1(k2_xboole_0(sK0,sK1))),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f10,f11,f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_finset_1(k2_xboole_0(X0,X1)) | ~v1_finset_1(X1) | ~v1_finset_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_finset_1(k2_xboole_0(X0,X1)) | ~v1_finset_1(X1) | ~v1_finset_1(X0))),
% 0.22/0.45    inference(flattening,[],[f6])).
% 0.22/0.45  fof(f6,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_finset_1(k2_xboole_0(X0,X1)) | (~v1_finset_1(X1) | ~v1_finset_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_finset_1(X1) & v1_finset_1(X0)) => v1_finset_1(k2_xboole_0(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_finset_1)).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    v1_finset_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    v1_finset_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (2640)------------------------------
% 0.22/0.45  % (2640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (2640)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (2640)Memory used [KB]: 9722
% 0.22/0.45  % (2640)Time elapsed: 0.025 s
% 0.22/0.45  % (2640)------------------------------
% 0.22/0.45  % (2640)------------------------------
% 0.22/0.45  % (2618)Success in time 0.091 s
%------------------------------------------------------------------------------
