%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  61 expanded)
%              Number of equality atoms :   34 (  40 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f14])).

fof(f14,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f8])).

fof(f8,negated_conjecture,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

fof(f70,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f65,f38])).

fof(f38,plain,(
    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f35,f15])).

fof(f15,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f35,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f29,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f29,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f22,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f22,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f65,plain,
    ( k1_xboole_0 != k2_relat_1(k4_relat_1(k1_xboole_0))
    | k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f37,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f37,plain,(
    v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f29,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:38:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.43  % (22210)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.45  % (22204)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.45  % (22204)Refutation not found, incomplete strategy% (22204)------------------------------
% 0.22/0.45  % (22204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (22204)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.45  
% 0.22/0.45  % (22204)Memory used [KB]: 10490
% 0.22/0.45  % (22204)Time elapsed: 0.032 s
% 0.22/0.45  % (22204)------------------------------
% 0.22/0.45  % (22204)------------------------------
% 0.22/0.46  % (22220)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.46  % (22220)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(subsumption_resolution,[],[f70,f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(flattening,[],[f8])).
% 0.22/0.46  fof(f8,negated_conjecture,(
% 0.22/0.46    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(negated_conjecture,[],[f7])).
% 0.22/0.46  fof(f7,conjecture,(
% 0.22/0.46    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).
% 0.22/0.46  fof(f70,plain,(
% 0.22/0.46    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f65,f38])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 0.22/0.46    inference(forward_demodulation,[],[f35,f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 0.22/0.46    inference(resolution,[],[f29,f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    v1_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(superposition,[],[f22,f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.46    inference(equality_resolution,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.46  fof(f65,plain,(
% 0.22/0.46    k1_xboole_0 != k2_relat_1(k4_relat_1(k1_xboole_0)) | k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(resolution,[],[f37,f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(flattening,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    v1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.22/0.46    inference(resolution,[],[f29,f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (22220)------------------------------
% 0.22/0.46  % (22220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (22220)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (22220)Memory used [KB]: 1663
% 0.22/0.46  % (22220)Time elapsed: 0.059 s
% 0.22/0.46  % (22220)------------------------------
% 0.22/0.46  % (22220)------------------------------
% 0.22/0.46  % (22202)Success in time 0.109 s
%------------------------------------------------------------------------------
