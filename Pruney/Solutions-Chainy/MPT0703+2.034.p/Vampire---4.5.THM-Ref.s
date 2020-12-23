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
% DateTime   : Thu Dec  3 12:54:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 168 expanded)
%              Number of leaves         :    9 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  121 ( 667 expanded)
%              Number of equality atoms :   19 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(subsumption_resolution,[],[f141,f45])).

fof(f45,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f35])).

fof(f35,plain,
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

fof(f141,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f139,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(k3_xboole_0(X1,k2_relat_1(sK2)),X1) ),
    inference(forward_demodulation,[],[f68,f67])).

fof(f67,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f66,f63])).

fof(f63,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f41,f46])).

fof(f46,plain,(
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

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f64,f41])).

fof(f64,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f42,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X1] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1) ),
    inference(subsumption_resolution,[],[f65,f41])).

fof(f65,plain,(
    ! [X1] :
      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f139,plain,(
    ! [X1] :
      ( ~ r1_tarski(k3_xboole_0(sK1,k2_relat_1(sK2)),X1)
      | r1_tarski(sK0,X1) ) ),
    inference(superposition,[],[f50,f115])).

fof(f115,plain,(
    k3_xboole_0(sK1,k2_relat_1(sK2)) = k2_xboole_0(sK0,k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(resolution,[],[f113,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f113,plain,(
    r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f112,f70])).

fof(f70,plain,(
    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f44,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f44,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f112,plain,(
    r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f111,f67])).

fof(f111,plain,(
    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f110,f67])).

fof(f110,plain,(
    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f81,f41])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k9_relat_1(X0,k10_relat_1(sK2,sK0)),k9_relat_1(X0,k10_relat_1(sK2,sK1))) ) ),
    inference(resolution,[],[f43,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f43,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:19:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (9178)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (9182)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (9194)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.57  % (9186)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.57  % (9186)Refutation not found, incomplete strategy% (9186)------------------------------
% 0.22/0.57  % (9186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (9186)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (9186)Memory used [KB]: 10746
% 0.22/0.57  % (9186)Time elapsed: 0.151 s
% 0.22/0.57  % (9186)------------------------------
% 0.22/0.57  % (9186)------------------------------
% 0.22/0.58  % (9200)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.58  % (9177)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.58  % (9190)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.58  % (9199)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.59  % (9191)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.59  % (9180)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.59  % (9176)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.59  % (9190)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.60  % (9179)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.60  % SZS output start Proof for theBenchmark
% 0.22/0.60  fof(f148,plain,(
% 0.22/0.60    $false),
% 0.22/0.60    inference(subsumption_resolution,[],[f141,f45])).
% 0.22/0.60  fof(f45,plain,(
% 0.22/0.60    ~r1_tarski(sK0,sK1)),
% 0.22/0.60    inference(cnf_transformation,[],[f36])).
% 0.22/0.60  fof(f36,plain,(
% 0.22/0.60    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f35])).
% 0.22/0.60  fof(f35,plain,(
% 0.22/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f21,plain,(
% 0.22/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.60    inference(flattening,[],[f20])).
% 0.22/0.60  fof(f20,plain,(
% 0.22/0.60    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.60    inference(ennf_transformation,[],[f19])).
% 0.22/0.60  fof(f19,negated_conjecture,(
% 0.22/0.60    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.60    inference(negated_conjecture,[],[f18])).
% 0.22/0.60  fof(f18,conjecture,(
% 0.22/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 0.22/0.60  fof(f141,plain,(
% 0.22/0.60    r1_tarski(sK0,sK1)),
% 0.22/0.60    inference(resolution,[],[f139,f69])).
% 0.22/0.60  fof(f69,plain,(
% 0.22/0.60    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,k2_relat_1(sK2)),X1)) )),
% 0.22/0.60    inference(forward_demodulation,[],[f68,f67])).
% 0.22/0.60  fof(f67,plain,(
% 0.22/0.60    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))) )),
% 0.22/0.60    inference(forward_demodulation,[],[f66,f63])).
% 0.22/0.60  fof(f63,plain,(
% 0.22/0.60    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.60    inference(resolution,[],[f41,f46])).
% 0.22/0.60  fof(f46,plain,(
% 0.22/0.60    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f22])).
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.60    inference(ennf_transformation,[],[f14])).
% 0.22/0.60  fof(f14,axiom,(
% 0.22/0.60    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.60  fof(f41,plain,(
% 0.22/0.60    v1_relat_1(sK2)),
% 0.22/0.60    inference(cnf_transformation,[],[f36])).
% 0.22/0.60  fof(f66,plain,(
% 0.22/0.60    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) )),
% 0.22/0.60    inference(subsumption_resolution,[],[f64,f41])).
% 0.22/0.60  fof(f64,plain,(
% 0.22/0.60    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) | ~v1_relat_1(sK2)) )),
% 0.22/0.60    inference(resolution,[],[f42,f59])).
% 0.22/0.60  fof(f59,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f34])).
% 0.22/0.60  fof(f34,plain,(
% 0.22/0.60    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.60    inference(flattening,[],[f33])).
% 0.22/0.60  fof(f33,plain,(
% 0.22/0.60    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.60    inference(ennf_transformation,[],[f17])).
% 0.22/0.60  fof(f17,axiom,(
% 0.22/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.22/0.60  fof(f42,plain,(
% 0.22/0.60    v1_funct_1(sK2)),
% 0.22/0.60    inference(cnf_transformation,[],[f36])).
% 0.22/0.60  fof(f68,plain,(
% 0.22/0.60    ( ! [X1] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1)) )),
% 0.22/0.60    inference(subsumption_resolution,[],[f65,f41])).
% 0.22/0.60  fof(f65,plain,(
% 0.22/0.60    ( ! [X1] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1) | ~v1_relat_1(sK2)) )),
% 0.22/0.60    inference(resolution,[],[f42,f56])).
% 0.22/0.60  fof(f56,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f30])).
% 0.22/0.60  fof(f30,plain,(
% 0.22/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.60    inference(flattening,[],[f29])).
% 0.22/0.60  fof(f29,plain,(
% 0.22/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.60    inference(ennf_transformation,[],[f16])).
% 0.22/0.60  fof(f16,axiom,(
% 0.22/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.22/0.60  fof(f139,plain,(
% 0.22/0.60    ( ! [X1] : (~r1_tarski(k3_xboole_0(sK1,k2_relat_1(sK2)),X1) | r1_tarski(sK0,X1)) )),
% 0.22/0.60    inference(superposition,[],[f50,f115])).
% 0.22/0.60  fof(f115,plain,(
% 0.22/0.60    k3_xboole_0(sK1,k2_relat_1(sK2)) = k2_xboole_0(sK0,k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 0.22/0.60    inference(resolution,[],[f113,f57])).
% 0.22/0.60  fof(f57,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.60    inference(cnf_transformation,[],[f31])).
% 0.22/0.60  fof(f31,plain,(
% 0.22/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.60    inference(ennf_transformation,[],[f4])).
% 0.22/0.60  fof(f4,axiom,(
% 0.22/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.60  fof(f113,plain,(
% 0.22/0.60    r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 0.22/0.60    inference(forward_demodulation,[],[f112,f70])).
% 0.22/0.60  fof(f70,plain,(
% 0.22/0.60    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))),
% 0.22/0.60    inference(resolution,[],[f44,f58])).
% 0.22/0.60  fof(f58,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f32])).
% 0.22/0.60  fof(f32,plain,(
% 0.22/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.60    inference(ennf_transformation,[],[f6])).
% 0.22/0.60  fof(f6,axiom,(
% 0.22/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.60  fof(f44,plain,(
% 0.22/0.60    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.22/0.60    inference(cnf_transformation,[],[f36])).
% 0.22/0.60  fof(f112,plain,(
% 0.22/0.60    r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 0.22/0.60    inference(forward_demodulation,[],[f111,f67])).
% 0.22/0.60  fof(f111,plain,(
% 0.22/0.60    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 0.22/0.60    inference(forward_demodulation,[],[f110,f67])).
% 0.22/0.60  fof(f110,plain,(
% 0.22/0.60    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))),
% 0.22/0.60    inference(resolution,[],[f81,f41])).
% 0.22/0.60  fof(f81,plain,(
% 0.22/0.60    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k9_relat_1(X0,k10_relat_1(sK2,sK0)),k9_relat_1(X0,k10_relat_1(sK2,sK1)))) )),
% 0.22/0.60    inference(resolution,[],[f43,f52])).
% 0.22/0.60  fof(f52,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f28])).
% 0.22/0.60  fof(f28,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.60    inference(flattening,[],[f27])).
% 0.22/0.60  fof(f27,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.60    inference(ennf_transformation,[],[f15])).
% 0.22/0.60  fof(f15,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.22/0.60  fof(f43,plain,(
% 0.22/0.60    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.22/0.60    inference(cnf_transformation,[],[f36])).
% 0.22/0.60  fof(f50,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f25])).
% 0.22/0.60  fof(f25,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.60    inference(ennf_transformation,[],[f3])).
% 0.22/0.60  fof(f3,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.60  % SZS output end Proof for theBenchmark
% 0.22/0.60  % (9190)------------------------------
% 0.22/0.60  % (9190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (9190)Termination reason: Refutation
% 0.22/0.60  
% 0.22/0.60  % (9190)Memory used [KB]: 1791
% 0.22/0.60  % (9190)Time elapsed: 0.170 s
% 0.22/0.60  % (9190)------------------------------
% 0.22/0.60  % (9190)------------------------------
% 0.22/0.60  % (9189)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.60  % (9175)Success in time 0.235 s
%------------------------------------------------------------------------------
