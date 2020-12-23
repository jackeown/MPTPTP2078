%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 159 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   18
%              Number of atoms          :  132 ( 523 expanded)
%              Number of equality atoms :   62 ( 207 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(subsumption_resolution,[],[f209,f143])).

fof(f143,plain,(
    k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f142,f52])).

fof(f52,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f26,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f142,plain,
    ( k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f141,f26])).

fof(f141,plain,
    ( k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f85,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f85,plain,(
    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f84,f47])).

fof(f47,plain,(
    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(resolution,[],[f26,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f84,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f83,f45])).

fof(f45,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f83,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f82,f52])).

fof(f82,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f81,f26])).

fof(f81,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f62,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f62,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f61,f58])).

fof(f58,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f57,f28])).

fof(f28,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,
    ( ~ v2_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f48,f27])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f26,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f61,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(backward_demodulation,[],[f25,f58])).

fof(f25,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f209,plain,(
    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f208,f46])).

fof(f46,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f26,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f208,plain,(
    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f207,f52])).

fof(f207,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f29,f107])).

fof(f107,plain,(
    k4_relat_1(sK0) = k7_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f97,f45])).

fof(f97,plain,(
    k4_relat_1(sK0) = k7_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:29:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (1166)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  % (1168)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (1176)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.49  % (1174)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.49  % (1168)Refutation not found, incomplete strategy% (1168)------------------------------
% 0.21/0.49  % (1168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1166)Refutation not found, incomplete strategy% (1166)------------------------------
% 0.21/0.50  % (1166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1166)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1166)Memory used [KB]: 10490
% 0.21/0.50  % (1166)Time elapsed: 0.068 s
% 0.21/0.50  % (1166)------------------------------
% 0.21/0.50  % (1166)------------------------------
% 0.21/0.50  % (1168)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1168)Memory used [KB]: 10618
% 0.21/0.50  % (1168)Time elapsed: 0.068 s
% 0.21/0.50  % (1168)------------------------------
% 0.21/0.50  % (1168)------------------------------
% 0.21/0.51  % (1158)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (1160)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (1169)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (1173)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (1175)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (1179)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.52  % (1163)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.52  % (1161)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.52  % (1161)Refutation not found, incomplete strategy% (1161)------------------------------
% 0.21/0.52  % (1161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1161)Memory used [KB]: 10490
% 0.21/0.52  % (1161)Time elapsed: 0.098 s
% 0.21/0.52  % (1161)------------------------------
% 0.21/0.52  % (1161)------------------------------
% 0.21/0.52  % (1179)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f209,f143])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f142,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.52    inference(resolution,[],[f26,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    v1_relat_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f141,f26])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.52    inference(superposition,[],[f85,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f84,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.21/0.52    inference(resolution,[],[f26,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.21/0.52    inference(forward_demodulation,[],[f83,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.52    inference(resolution,[],[f26,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f82,f52])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f81,f26])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.52    inference(superposition,[],[f62,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.21/0.52    inference(forward_demodulation,[],[f61,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f57,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    v2_funct_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~v2_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f48,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    v1_funct_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f26,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.52    inference(backward_demodulation,[],[f25,f58])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f208,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.21/0.52    inference(resolution,[],[f26,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f207,f52])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.52    inference(superposition,[],[f29,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    k4_relat_1(sK0) = k7_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f97,f45])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    k4_relat_1(sK0) = k7_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))),
% 0.21/0.52    inference(resolution,[],[f52,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (1179)------------------------------
% 0.21/0.52  % (1179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1179)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (1179)Memory used [KB]: 1791
% 0.21/0.52  % (1179)Time elapsed: 0.083 s
% 0.21/0.52  % (1179)------------------------------
% 0.21/0.52  % (1179)------------------------------
% 0.21/0.52  % (1157)Success in time 0.156 s
%------------------------------------------------------------------------------
