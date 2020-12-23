%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 221 expanded)
%              Number of leaves         :   12 (  60 expanded)
%              Depth                    :   21
%              Number of atoms          :  158 ( 520 expanded)
%              Number of equality atoms :   46 ( 186 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(subsumption_resolution,[],[f303,f165])).

fof(f165,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f158,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f158,plain,(
    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f153,f30])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f153,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f109,f149])).

fof(f149,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f148,f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f148,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f147,f30])).

fof(f147,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f145,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f145,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK0))
    | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f76,f31])).

fof(f31,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(sK0))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK0,X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f42,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f42,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(sK0))
      | k2_relat_1(X1) = k2_relat_1(k5_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f109,plain,
    ( ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f90,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f90,plain,(
    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f54,f30])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(k5_relat_1(sK0,X0)) ) ),
    inference(resolution,[],[f47,f34])).

fof(f47,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | v1_relat_1(k5_relat_1(sK0,X4)) ) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f303,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f29,f280])).

fof(f280,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f214,f35])).

fof(f214,plain,(
    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f209,f30])).

fof(f209,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f129,f205])).

fof(f205,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f185,f31])).

fof(f185,plain,(
    k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f159,f165])).

fof(f159,plain,(
    k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0)) ),
    inference(subsumption_resolution,[],[f156,f33])).

fof(f156,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0)) ),
    inference(backward_demodulation,[],[f115,f149])).

fof(f115,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_relat_1(sK0))
    | k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0)) ),
    inference(resolution,[],[f90,f44])).

fof(f44,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(sK0))
      | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,sK0)) ) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f129,plain,
    ( ~ v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f95,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f95,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f66,f30])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(k5_relat_1(X0,sK0)) ) ),
    inference(resolution,[],[f48,f34])).

fof(f48,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | v1_relat_1(k5_relat_1(X5,sK0)) ) ),
    inference(resolution,[],[f28,f40])).

fof(f29,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:39:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.46  % (22598)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.47  % (22590)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.51  % (22601)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (22593)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.53  % (22586)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.53  % (22591)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.53  % (22593)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f304,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f303,f165])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f158,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f153,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.53    inference(backward_demodulation,[],[f109,f149])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.53    inference(forward_demodulation,[],[f148,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.53  fof(f148,plain,(
% 0.20/0.53    k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f147,f30])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f145,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    ~r1_tarski(k1_xboole_0,k2_relat_1(sK0)) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(superposition,[],[f76,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(sK0)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK0,X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(resolution,[],[f42,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(sK0)) | k2_relat_1(X1) = k2_relat_1(k5_relat_1(sK0,X1))) )),
% 0.20/0.53    inference(resolution,[],[f28,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    v1_relat_1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.53    inference(negated_conjecture,[],[f11])).
% 0.20/0.53  fof(f11,conjecture,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ~v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.53    inference(resolution,[],[f90,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.53    inference(resolution,[],[f54,f30])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(k5_relat_1(sK0,X0))) )),
% 0.20/0.53    inference(resolution,[],[f47,f34])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X4] : (~v1_relat_1(X4) | v1_relat_1(k5_relat_1(sK0,X4))) )),
% 0.20/0.53    inference(resolution,[],[f28,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f283])).
% 0.20/0.54  fof(f283,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.54    inference(backward_demodulation,[],[f29,f280])).
% 0.20/0.54  fof(f280,plain,(
% 0.20/0.54    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.54    inference(resolution,[],[f214,f35])).
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f209,f30])).
% 0.20/0.54  fof(f209,plain,(
% 0.20/0.54    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.54    inference(backward_demodulation,[],[f129,f205])).
% 0.20/0.54  fof(f205,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.54    inference(forward_demodulation,[],[f185,f31])).
% 0.20/0.54  fof(f185,plain,(
% 0.20/0.54    k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.54    inference(backward_demodulation,[],[f159,f165])).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f156,f33])).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0))),
% 0.20/0.54    inference(backward_demodulation,[],[f115,f149])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    ~r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_relat_1(sK0)) | k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0))),
% 0.20/0.54    inference(resolution,[],[f90,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X3] : (~v1_relat_1(X3) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(sK0)) | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,sK0))) )),
% 0.20/0.54    inference(resolution,[],[f28,f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    ~v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.54    inference(resolution,[],[f95,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.54    inference(resolution,[],[f66,f30])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(k5_relat_1(X0,sK0))) )),
% 0.20/0.54    inference(resolution,[],[f48,f34])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X5] : (~v1_relat_1(X5) | v1_relat_1(k5_relat_1(X5,sK0))) )),
% 0.20/0.54    inference(resolution,[],[f28,f40])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (22593)------------------------------
% 0.20/0.54  % (22593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22593)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (22593)Memory used [KB]: 1791
% 0.20/0.54  % (22593)Time elapsed: 0.111 s
% 0.20/0.54  % (22593)------------------------------
% 0.20/0.54  % (22593)------------------------------
% 0.20/0.54  % (22580)Success in time 0.19 s
%------------------------------------------------------------------------------
