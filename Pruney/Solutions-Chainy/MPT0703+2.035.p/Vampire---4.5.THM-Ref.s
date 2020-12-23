%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 172 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  128 ( 674 expanded)
%              Number of equality atoms :   19 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(subsumption_resolution,[],[f222,f42])).

fof(f42,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f222,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f213,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f213,plain,(
    r1_tarski(k2_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f87,f113])).

fof(f113,plain,(
    r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f112,f65])).

fof(f65,plain,(
    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f41,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f41,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f112,plain,(
    r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f111,f62])).

fof(f62,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f61,f58])).

fof(f58,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f59,f38])).

fof(f59,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f39,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,(
    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f110,f62])).

fof(f110,plain,(
    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f76,f38])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k9_relat_1(X0,k10_relat_1(sK2,sK0)),k9_relat_1(X0,k10_relat_1(sK2,sK1))) ) ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f40,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X2,k2_relat_1(sK2)))
      | r1_tarski(k2_xboole_0(X3,X2),X2) ) ),
    inference(superposition,[],[f45,f70])).

fof(f70,plain,(
    ! [X1] : k2_xboole_0(k3_xboole_0(X1,k2_relat_1(sK2)),X1) = X1 ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f64,plain,(
    ! [X1] : r1_tarski(k3_xboole_0(X1,k2_relat_1(sK2)),X1) ),
    inference(forward_demodulation,[],[f63,f62])).

fof(f63,plain,(
    ! [X1] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1) ),
    inference(subsumption_resolution,[],[f60,f38])).

fof(f60,plain,(
    ! [X1] :
      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f39,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

% (18280)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:27:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (18271)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (18262)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (18279)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (18271)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 1.22/0.52  % (18261)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.52  % (18263)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.52  % (18267)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.52  % SZS output start Proof for theBenchmark
% 1.22/0.52  fof(f227,plain,(
% 1.22/0.52    $false),
% 1.22/0.52    inference(subsumption_resolution,[],[f222,f42])).
% 1.22/0.52  fof(f42,plain,(
% 1.22/0.52    ~r1_tarski(sK0,sK1)),
% 1.22/0.52    inference(cnf_transformation,[],[f35])).
% 1.22/0.52  fof(f35,plain,(
% 1.22/0.52    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f34])).
% 1.22/0.52  fof(f34,plain,(
% 1.22/0.52    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.22/0.52    inference(flattening,[],[f20])).
% 1.22/0.52  fof(f20,plain,(
% 1.22/0.52    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.22/0.52    inference(ennf_transformation,[],[f19])).
% 1.22/0.52  fof(f19,negated_conjecture,(
% 1.22/0.52    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.22/0.52    inference(negated_conjecture,[],[f18])).
% 1.22/0.52  fof(f18,conjecture,(
% 1.22/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 1.22/0.52  fof(f222,plain,(
% 1.22/0.52    r1_tarski(sK0,sK1)),
% 1.22/0.52    inference(resolution,[],[f213,f44])).
% 1.22/0.52  fof(f44,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f23])).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.22/0.52    inference(ennf_transformation,[],[f3])).
% 1.22/0.52  fof(f3,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.22/0.52  fof(f213,plain,(
% 1.22/0.52    r1_tarski(k2_xboole_0(sK0,sK1),sK1)),
% 1.22/0.52    inference(resolution,[],[f87,f113])).
% 1.22/0.52  fof(f113,plain,(
% 1.22/0.52    r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 1.22/0.52    inference(forward_demodulation,[],[f112,f65])).
% 1.22/0.52  fof(f65,plain,(
% 1.22/0.52    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))),
% 1.22/0.52    inference(resolution,[],[f41,f53])).
% 1.22/0.52  fof(f53,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.22/0.52    inference(cnf_transformation,[],[f31])).
% 1.22/0.52  fof(f31,plain,(
% 1.22/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.22/0.52    inference(ennf_transformation,[],[f5])).
% 1.22/0.52  fof(f5,axiom,(
% 1.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.22/0.52  fof(f41,plain,(
% 1.22/0.52    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.22/0.52    inference(cnf_transformation,[],[f35])).
% 1.22/0.52  fof(f112,plain,(
% 1.22/0.52    r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 1.22/0.52    inference(forward_demodulation,[],[f111,f62])).
% 1.22/0.52  fof(f62,plain,(
% 1.22/0.52    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))) )),
% 1.22/0.52    inference(forward_demodulation,[],[f61,f58])).
% 1.22/0.52  fof(f58,plain,(
% 1.22/0.52    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 1.22/0.52    inference(resolution,[],[f38,f43])).
% 1.22/0.52  fof(f43,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f22])).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f14])).
% 1.22/0.52  fof(f14,axiom,(
% 1.22/0.52    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.22/0.52  fof(f38,plain,(
% 1.22/0.52    v1_relat_1(sK2)),
% 1.22/0.52    inference(cnf_transformation,[],[f35])).
% 1.22/0.52  fof(f61,plain,(
% 1.22/0.52    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) )),
% 1.22/0.52    inference(subsumption_resolution,[],[f59,f38])).
% 1.22/0.52  fof(f59,plain,(
% 1.22/0.52    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) | ~v1_relat_1(sK2)) )),
% 1.22/0.52    inference(resolution,[],[f39,f54])).
% 1.22/0.52  fof(f54,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f33])).
% 1.22/0.52  fof(f33,plain,(
% 1.22/0.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.22/0.52    inference(flattening,[],[f32])).
% 1.22/0.52  fof(f32,plain,(
% 1.22/0.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.22/0.52    inference(ennf_transformation,[],[f17])).
% 1.22/0.52  fof(f17,axiom,(
% 1.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 1.22/0.52  fof(f39,plain,(
% 1.22/0.52    v1_funct_1(sK2)),
% 1.22/0.52    inference(cnf_transformation,[],[f35])).
% 1.22/0.52  fof(f111,plain,(
% 1.22/0.52    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 1.22/0.52    inference(forward_demodulation,[],[f110,f62])).
% 1.22/0.52  fof(f110,plain,(
% 1.22/0.52    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))),
% 1.22/0.52    inference(resolution,[],[f76,f38])).
% 1.22/0.52  fof(f76,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k9_relat_1(X0,k10_relat_1(sK2,sK0)),k9_relat_1(X0,k10_relat_1(sK2,sK1)))) )),
% 1.22/0.52    inference(resolution,[],[f40,f47])).
% 1.22/0.52  fof(f47,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f27])).
% 1.22/0.52  fof(f27,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.22/0.52    inference(flattening,[],[f26])).
% 1.22/0.52  fof(f26,plain,(
% 1.22/0.52    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.22/0.52    inference(ennf_transformation,[],[f15])).
% 1.22/0.52  fof(f15,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 1.22/0.52  fof(f40,plain,(
% 1.22/0.52    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.22/0.52    inference(cnf_transformation,[],[f35])).
% 1.22/0.52  fof(f87,plain,(
% 1.22/0.52    ( ! [X2,X3] : (~r1_tarski(X3,k3_xboole_0(X2,k2_relat_1(sK2))) | r1_tarski(k2_xboole_0(X3,X2),X2)) )),
% 1.22/0.52    inference(superposition,[],[f45,f70])).
% 1.22/0.52  fof(f70,plain,(
% 1.22/0.52    ( ! [X1] : (k2_xboole_0(k3_xboole_0(X1,k2_relat_1(sK2)),X1) = X1) )),
% 1.22/0.52    inference(resolution,[],[f64,f52])).
% 1.22/0.52  fof(f52,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.22/0.52    inference(cnf_transformation,[],[f30])).
% 1.22/0.52  fof(f30,plain,(
% 1.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.22/0.52    inference(ennf_transformation,[],[f4])).
% 1.22/0.52  fof(f4,axiom,(
% 1.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.22/0.52  fof(f64,plain,(
% 1.22/0.52    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,k2_relat_1(sK2)),X1)) )),
% 1.22/0.52    inference(forward_demodulation,[],[f63,f62])).
% 1.22/0.52  fof(f63,plain,(
% 1.22/0.52    ( ! [X1] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1)) )),
% 1.22/0.52    inference(subsumption_resolution,[],[f60,f38])).
% 1.22/0.52  fof(f60,plain,(
% 1.22/0.52    ( ! [X1] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1) | ~v1_relat_1(sK2)) )),
% 1.22/0.52    inference(resolution,[],[f39,f51])).
% 1.22/0.52  fof(f51,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f29])).
% 1.22/0.52  fof(f29,plain,(
% 1.22/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.22/0.52    inference(flattening,[],[f28])).
% 1.22/0.52  % (18280)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.22/0.52  fof(f28,plain,(
% 1.22/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.22/0.52    inference(ennf_transformation,[],[f16])).
% 1.22/0.52  fof(f16,axiom,(
% 1.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.22/0.52  fof(f45,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f24])).
% 1.22/0.52  fof(f24,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 1.22/0.52    inference(ennf_transformation,[],[f6])).
% 1.22/0.52  fof(f6,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
% 1.22/0.52  % SZS output end Proof for theBenchmark
% 1.22/0.52  % (18271)------------------------------
% 1.22/0.52  % (18271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (18271)Termination reason: Refutation
% 1.22/0.52  
% 1.22/0.52  % (18271)Memory used [KB]: 1791
% 1.22/0.52  % (18271)Time elapsed: 0.106 s
% 1.22/0.52  % (18271)------------------------------
% 1.22/0.52  % (18271)------------------------------
% 1.22/0.52  % (18256)Success in time 0.162 s
%------------------------------------------------------------------------------
