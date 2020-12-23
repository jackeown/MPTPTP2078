%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:12 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 192 expanded)
%              Number of leaves         :    9 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  106 ( 488 expanded)
%              Number of equality atoms :   20 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (25384)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f2630,plain,(
    $false ),
    inference(resolution,[],[f2576,f35])).

fof(f35,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f2576,plain,(
    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f2561,f66])).

fof(f66,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f2561,plain,(
    r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f2461,f2544,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f2544,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(superposition,[],[f2332,f54])).

fof(f54,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f37])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f2332,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f2318,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f2318,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(superposition,[],[f45,f231])).

fof(f231,plain,(
    k2_relat_1(sK1) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f60,f229])).

fof(f229,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f71,f132,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f132,plain,(
    ! [X0] : r1_tarski(sK1,k2_xboole_0(X0,sK1)) ),
    inference(forward_demodulation,[],[f125,f127])).

fof(f127,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f45,f74,f44])).

fof(f74,plain,(
    r1_tarski(k2_xboole_0(sK1,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f48,f34,f38])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f125,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f74,f41])).

fof(f71,plain,(
    r1_tarski(k2_xboole_0(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f48,f34,f38])).

fof(f60,plain,(
    k2_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f36,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2461,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f531,f2451,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f2451,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f45,f232])).

fof(f232,plain,(
    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f64,f229])).

fof(f64,plain,(
    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f36,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f531,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f45,f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (25364)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.47  % (25356)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.47  % (25383)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.48  % (25373)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.48  % (25380)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.49  % (25381)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.51  % (25357)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.51  % (25375)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.52  % (25359)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.52  % (25358)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.53  % (25378)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.53  % (25377)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.53  % (25369)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.53  % (25354)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.53  % (25380)Refutation found. Thanks to Tanya!
% 1.38/0.53  % SZS status Theorem for theBenchmark
% 1.38/0.53  % (25367)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.53  % SZS output start Proof for theBenchmark
% 1.38/0.53  % (25384)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.53  fof(f2630,plain,(
% 1.38/0.53    $false),
% 1.38/0.53    inference(resolution,[],[f2576,f35])).
% 1.38/0.53  fof(f35,plain,(
% 1.38/0.53    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 1.38/0.53    inference(cnf_transformation,[],[f23])).
% 1.38/0.53  fof(f23,plain,(
% 1.38/0.53    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.38/0.53    inference(flattening,[],[f22])).
% 1.38/0.53  fof(f22,plain,(
% 1.38/0.53    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.38/0.53    inference(ennf_transformation,[],[f21])).
% 1.38/0.53  fof(f21,negated_conjecture,(
% 1.38/0.53    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.38/0.53    inference(negated_conjecture,[],[f20])).
% 1.38/0.53  fof(f20,conjecture,(
% 1.38/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 1.38/0.53  fof(f2576,plain,(
% 1.38/0.53    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 1.38/0.53    inference(forward_demodulation,[],[f2561,f66])).
% 1.38/0.53  fof(f66,plain,(
% 1.38/0.53    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f36,f37])).
% 1.38/0.53  fof(f37,plain,(
% 1.38/0.53    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f24])).
% 1.38/0.53  fof(f24,plain,(
% 1.38/0.53    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.38/0.53    inference(ennf_transformation,[],[f17])).
% 1.38/0.53  fof(f17,axiom,(
% 1.38/0.53    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.38/0.53  fof(f36,plain,(
% 1.38/0.53    v1_relat_1(sK0)),
% 1.38/0.53    inference(cnf_transformation,[],[f23])).
% 1.38/0.53  fof(f2561,plain,(
% 1.38/0.53    r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f2461,f2544,f38])).
% 1.38/0.53  fof(f38,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f26])).
% 1.38/0.53  fof(f26,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.38/0.53    inference(flattening,[],[f25])).
% 1.38/0.53  fof(f25,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.38/0.53    inference(ennf_transformation,[],[f11])).
% 1.38/0.53  fof(f11,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.38/0.53  fof(f2544,plain,(
% 1.38/0.53    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 1.38/0.53    inference(superposition,[],[f2332,f54])).
% 1.38/0.53  fof(f54,plain,(
% 1.38/0.53    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f33,f37])).
% 1.38/0.53  fof(f33,plain,(
% 1.38/0.53    v1_relat_1(sK1)),
% 1.38/0.53    inference(cnf_transformation,[],[f23])).
% 1.38/0.53  fof(f2332,plain,(
% 1.38/0.53    ( ! [X0] : (r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1)))) )),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f2318,f41])).
% 1.38/0.53  fof(f41,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f30])).
% 1.38/0.53  fof(f30,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.38/0.53    inference(ennf_transformation,[],[f3])).
% 1.38/0.53  fof(f3,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.38/0.53  fof(f2318,plain,(
% 1.38/0.53    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.38/0.53    inference(superposition,[],[f45,f231])).
% 1.38/0.53  fof(f231,plain,(
% 1.38/0.53    k2_relat_1(sK1) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.38/0.53    inference(backward_demodulation,[],[f60,f229])).
% 1.38/0.53  fof(f229,plain,(
% 1.38/0.53    sK1 = k2_xboole_0(sK0,sK1)),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f71,f132,f44])).
% 1.38/0.53  fof(f44,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.38/0.53    inference(cnf_transformation,[],[f2])).
% 1.38/0.53  fof(f2,axiom,(
% 1.38/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.53  fof(f132,plain,(
% 1.38/0.53    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(X0,sK1))) )),
% 1.38/0.53    inference(forward_demodulation,[],[f125,f127])).
% 1.38/0.53  fof(f127,plain,(
% 1.38/0.53    sK1 = k2_xboole_0(sK1,sK0)),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f45,f74,f44])).
% 1.38/0.53  fof(f74,plain,(
% 1.38/0.53    r1_tarski(k2_xboole_0(sK1,sK0),sK1)),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f48,f34,f38])).
% 1.38/0.53  fof(f34,plain,(
% 1.38/0.53    r1_tarski(sK0,sK1)),
% 1.38/0.53    inference(cnf_transformation,[],[f23])).
% 1.38/0.53  fof(f48,plain,(
% 1.38/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.38/0.53    inference(equality_resolution,[],[f43])).
% 1.38/0.53  fof(f43,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.38/0.53    inference(cnf_transformation,[],[f2])).
% 1.38/0.53  fof(f125,plain,(
% 1.38/0.53    ( ! [X0] : (r1_tarski(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK1))) )),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f74,f41])).
% 1.38/0.53  fof(f71,plain,(
% 1.38/0.53    r1_tarski(k2_xboole_0(sK0,sK1),sK1)),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f48,f34,f38])).
% 1.38/0.53  fof(f60,plain,(
% 1.38/0.53    k2_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f33,f36,f47])).
% 1.38/0.53  fof(f47,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f32])).
% 1.38/0.53  fof(f32,plain,(
% 1.38/0.53    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.38/0.53    inference(ennf_transformation,[],[f19])).
% 1.38/0.53  fof(f19,axiom,(
% 1.38/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).
% 1.38/0.53  fof(f45,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f10])).
% 1.38/0.53  fof(f10,axiom,(
% 1.38/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.38/0.53  fof(f2461,plain,(
% 1.38/0.53    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f531,f2451,f39])).
% 1.38/0.53  fof(f39,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f28])).
% 1.38/0.53  fof(f28,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.38/0.53    inference(flattening,[],[f27])).
% 1.38/0.53  fof(f27,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.38/0.53    inference(ennf_transformation,[],[f5])).
% 1.38/0.53  fof(f5,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.38/0.53  fof(f2451,plain,(
% 1.38/0.53    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 1.38/0.53    inference(superposition,[],[f45,f232])).
% 1.38/0.53  fof(f232,plain,(
% 1.38/0.53    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 1.38/0.53    inference(backward_demodulation,[],[f64,f229])).
% 1.38/0.53  fof(f64,plain,(
% 1.38/0.53    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 1.38/0.53    inference(unit_resulting_resolution,[],[f33,f36,f46])).
% 1.38/0.53  fof(f46,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f31])).
% 1.38/0.53  fof(f31,plain,(
% 1.38/0.53    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.38/0.53    inference(ennf_transformation,[],[f18])).
% 1.38/0.53  fof(f18,axiom,(
% 1.38/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 1.38/0.53  fof(f531,plain,(
% 1.38/0.53    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 1.38/0.53    inference(superposition,[],[f45,f54])).
% 1.38/0.53  % SZS output end Proof for theBenchmark
% 1.38/0.53  % (25380)------------------------------
% 1.38/0.53  % (25380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (25380)Termination reason: Refutation
% 1.38/0.53  
% 1.38/0.53  % (25380)Memory used [KB]: 6908
% 1.38/0.53  % (25380)Time elapsed: 0.125 s
% 1.38/0.53  % (25380)------------------------------
% 1.38/0.53  % (25380)------------------------------
% 1.38/0.53  % (25353)Success in time 0.182 s
%------------------------------------------------------------------------------
