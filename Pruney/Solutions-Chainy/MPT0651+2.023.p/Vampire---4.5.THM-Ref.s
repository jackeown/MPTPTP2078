%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 217 expanded)
%              Number of leaves         :    9 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  168 ( 737 expanded)
%              Number of equality atoms :   55 ( 270 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (17983)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (17990)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% (18004)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% (18002)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% (17991)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% (17982)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% (17995)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% (17994)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% (18000)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% (17984)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% (17992)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% (17984)Refutation not found, incomplete strategy% (17984)------------------------------
% (17984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17984)Termination reason: Refutation not found, incomplete strategy

% (17984)Memory used [KB]: 10618
% (17984)Time elapsed: 0.112 s
% (17984)------------------------------
% (17984)------------------------------
% (17992)Refutation not found, incomplete strategy% (17992)------------------------------
% (17992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17992)Termination reason: Refutation not found, incomplete strategy

% (17992)Memory used [KB]: 10618
% (17992)Time elapsed: 0.115 s
% (17992)------------------------------
% (17992)------------------------------
% (17998)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
fof(f207,plain,(
    $false ),
    inference(subsumption_resolution,[],[f206,f195])).

fof(f195,plain,(
    ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f194,f90])).

fof(f90,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f89,f51])).

fof(f51,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f89,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f88,f28])).

fof(f88,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f87,f57])).

fof(f57,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f28,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f87,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f86,f52])).

fof(f52,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) ),
    inference(superposition,[],[f67,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f67,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f66,f63])).

fof(f63,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f62,f30])).

fof(f30,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,
    ( ~ v2_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f54,f29])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f66,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(backward_demodulation,[],[f27,f63])).

fof(f27,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f194,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f189,f57])).

fof(f189,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(superposition,[],[f49,f51])).

fof(f49,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X2)) ) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f206,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f167,f205])).

fof(f205,plain,(
    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f204,f51])).

fof(f204,plain,(
    k1_relat_1(k4_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(subsumption_resolution,[],[f203,f57])).

fof(f203,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | k1_relat_1(k4_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(subsumption_resolution,[],[f198,f131])).

fof(f131,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f130,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f130,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f128,f28])).

fof(f128,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK0))) ),
    inference(superposition,[],[f41,f53])).

fof(f53,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f198,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | k1_relat_1(k4_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(superposition,[],[f50,f52])).

fof(f50,plain,(
    ! [X3] :
      ( ~ r1_tarski(k2_relat_1(X3),k1_relat_1(sK0))
      | ~ v1_relat_1(X3)
      | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,sK0)) ) ),
    inference(resolution,[],[f28,f34])).

fof(f167,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f163,f51])).

fof(f163,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)),k1_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f56,f57])).

fof(f56,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | r1_tarski(k1_relat_1(k5_relat_1(X5,sK0)),k1_relat_1(X5)) ) ),
    inference(resolution,[],[f28,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:30:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (17985)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (17981)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (18005)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.50  % (17988)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (17997)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (18005)Refutation not found, incomplete strategy% (18005)------------------------------
% 0.22/0.50  % (18005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18005)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (18005)Memory used [KB]: 10618
% 0.22/0.50  % (18005)Time elapsed: 0.049 s
% 0.22/0.50  % (18005)------------------------------
% 0.22/0.50  % (18005)------------------------------
% 0.22/0.51  % (17986)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (18001)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (17989)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (17989)Refutation not found, incomplete strategy% (17989)------------------------------
% 0.22/0.51  % (17989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17989)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17989)Memory used [KB]: 6140
% 0.22/0.51  % (17989)Time elapsed: 0.063 s
% 0.22/0.51  % (17989)------------------------------
% 0.22/0.51  % (17989)------------------------------
% 0.22/0.51  % (18003)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (17999)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (18003)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.52  % (17983)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (17990)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (18004)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.52  % (18002)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (17991)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (17982)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (17995)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (17994)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (18000)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.53  % (17984)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.53  % (17992)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  % (17984)Refutation not found, incomplete strategy% (17984)------------------------------
% 0.22/0.53  % (17984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17984)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17984)Memory used [KB]: 10618
% 0.22/0.53  % (17984)Time elapsed: 0.112 s
% 0.22/0.53  % (17984)------------------------------
% 0.22/0.53  % (17984)------------------------------
% 0.22/0.53  % (17992)Refutation not found, incomplete strategy% (17992)------------------------------
% 0.22/0.53  % (17992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17992)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17992)Memory used [KB]: 10618
% 0.22/0.53  % (17992)Time elapsed: 0.115 s
% 0.22/0.53  % (17992)------------------------------
% 0.22/0.53  % (17992)------------------------------
% 0.22/0.53  % (17998)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f206,f195])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f194,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.22/0.53    inference(forward_demodulation,[],[f89,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.22/0.53    inference(resolution,[],[f28,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f88,f28])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f87,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.53    inference(resolution,[],[f28,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f86,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.22/0.53    inference(resolution,[],[f28,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0)) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))),
% 0.22/0.53    inference(superposition,[],[f67,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.22/0.53    inference(forward_demodulation,[],[f66,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f62,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    v2_funct_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ~v2_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f54,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    v1_funct_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.53    inference(resolution,[],[f28,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.53    inference(backward_demodulation,[],[f27,f63])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f189,f57])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.22/0.53    inference(superposition,[],[f49,f51])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X2] : (~r1_tarski(k2_relat_1(sK0),k1_relat_1(X2)) | ~v1_relat_1(X2) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X2))) )),
% 0.22/0.53    inference(resolution,[],[f28,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.53    inference(backward_demodulation,[],[f167,f205])).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.22/0.53    inference(forward_demodulation,[],[f204,f51])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    k1_relat_1(k4_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f203,f57])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ~v1_relat_1(k4_relat_1(sK0)) | k1_relat_1(k4_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f198,f131])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f130,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK0)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f128,f28])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK0)))),
% 0.22/0.53    inference(superposition,[],[f41,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.22/0.53    inference(resolution,[],[f28,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | k1_relat_1(k4_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.22/0.53    inference(superposition,[],[f50,f52])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X3] : (~r1_tarski(k2_relat_1(X3),k1_relat_1(sK0)) | ~v1_relat_1(X3) | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,sK0))) )),
% 0.22/0.53    inference(resolution,[],[f28,f34])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)),k2_relat_1(sK0))),
% 0.22/0.53    inference(forward_demodulation,[],[f163,f51])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)),k1_relat_1(k4_relat_1(sK0)))),
% 0.22/0.53    inference(resolution,[],[f56,f57])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X5] : (~v1_relat_1(X5) | r1_tarski(k1_relat_1(k5_relat_1(X5,sK0)),k1_relat_1(X5))) )),
% 0.22/0.53    inference(resolution,[],[f28,f41])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (18003)------------------------------
% 0.22/0.53  % (18003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18003)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (18003)Memory used [KB]: 1663
% 0.22/0.53  % (18003)Time elapsed: 0.097 s
% 0.22/0.53  % (18003)------------------------------
% 0.22/0.53  % (18003)------------------------------
% 0.22/0.53  % (17980)Success in time 0.17 s
%------------------------------------------------------------------------------
