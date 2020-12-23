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
% DateTime   : Thu Dec  3 12:51:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   10 (  11 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f8,f9,f7])).

fof(f7,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK1)
    | ~ v4_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK1)
    | ~ v4_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1] :
        ( ~ v5_relat_1(k1_xboole_0,X1)
        | ~ v4_relat_1(k1_xboole_0,X0) )
   => ( ~ v5_relat_1(k1_xboole_0,sK1)
      | ~ v4_relat_1(k1_xboole_0,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ~ v5_relat_1(k1_xboole_0,X1)
      | ~ v4_relat_1(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v5_relat_1(k1_xboole_0,X1)
        & v4_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t206_relat_1)).

fof(f9,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

fof(f8,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (19469)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.47  % (19473)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.47  % (19469)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f8,f9,f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ~v5_relat_1(k1_xboole_0,sK1) | ~v4_relat_1(k1_xboole_0,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ~v5_relat_1(k1_xboole_0,sK1) | ~v4_relat_1(k1_xboole_0,sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f5])).
% 0.22/0.47  fof(f5,plain,(
% 0.22/0.47    ? [X0,X1] : (~v5_relat_1(k1_xboole_0,X1) | ~v4_relat_1(k1_xboole_0,X0)) => (~v5_relat_1(k1_xboole_0,sK1) | ~v4_relat_1(k1_xboole_0,sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f4,plain,(
% 0.22/0.47    ? [X0,X1] : (~v5_relat_1(k1_xboole_0,X1) | ~v4_relat_1(k1_xboole_0,X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.22/0.47    inference(negated_conjecture,[],[f2])).
% 0.22/0.47  fof(f2,conjecture,(
% 0.22/0.47    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t206_relat_1)).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (19469)------------------------------
% 0.22/0.47  % (19469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (19469)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (19469)Memory used [KB]: 767
% 0.22/0.47  % (19469)Time elapsed: 0.052 s
% 0.22/0.47  % (19469)------------------------------
% 0.22/0.47  % (19469)------------------------------
% 0.22/0.47  % (19463)Success in time 0.11 s
%------------------------------------------------------------------------------
