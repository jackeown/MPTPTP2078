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
% DateTime   : Thu Dec  3 12:52:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 254 expanded)
%              Number of leaves         :    8 (  46 expanded)
%              Depth                    :   19
%              Number of atoms          :  149 ( 919 expanded)
%              Number of equality atoms :   66 ( 351 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8626)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f116,plain,(
    $false ),
    inference(subsumption_resolution,[],[f115,f38])).

fof(f38,plain,(
    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(resolution,[],[f22,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f115,plain,(
    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f114,f50])).

fof(f50,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f44,f48])).

fof(f48,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f47,f24])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,
    ( ~ v2_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f41,f23])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f22,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f44,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f43,f24])).

fof(f43,plain,
    ( ~ v2_funct_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f33,f23])).

fof(f33,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f114,plain,(
    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f113,f42])).

fof(f42,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f113,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f112,f22])).

fof(f112,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f90,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f90,plain,(
    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(backward_demodulation,[],[f73,f88])).

fof(f88,plain,(
    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f87,f49])).

fof(f49,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f46,f48])).

fof(f46,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f45,f24])).

fof(f45,plain,
    ( ~ v2_funct_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f34,f23])).

fof(f34,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,(
    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f78,f50])).

fof(f78,plain,(
    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f73,plain,
    ( k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f72,f42])).

fof(f72,plain,
    ( k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f71,f22])).

fof(f71,plain,
    ( k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f52,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f52,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f51,f48])).

fof(f51,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(backward_demodulation,[],[f21,f48])).

fof(f21,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:50:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (8618)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.46  % (8618)Refutation not found, incomplete strategy% (8618)------------------------------
% 0.20/0.46  % (8618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (8618)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (8618)Memory used [KB]: 10490
% 0.20/0.46  % (8618)Time elapsed: 0.065 s
% 0.20/0.46  % (8618)------------------------------
% 0.20/0.46  % (8618)------------------------------
% 0.20/0.48  % (8631)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.48  % (8631)Refutation not found, incomplete strategy% (8631)------------------------------
% 0.20/0.48  % (8631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (8631)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (8631)Memory used [KB]: 1535
% 0.20/0.48  % (8631)Time elapsed: 0.075 s
% 0.20/0.48  % (8631)------------------------------
% 0.20/0.48  % (8631)------------------------------
% 0.20/0.49  % (8623)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.49  % (8623)Refutation not found, incomplete strategy% (8623)------------------------------
% 0.20/0.49  % (8623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8623)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8623)Memory used [KB]: 10490
% 0.20/0.49  % (8623)Time elapsed: 0.082 s
% 0.20/0.49  % (8623)------------------------------
% 0.20/0.49  % (8623)------------------------------
% 0.20/0.50  % (8637)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (8620)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (8616)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (8619)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (8615)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (8632)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (8629)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (8636)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.51  % (8630)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.51  % (8617)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (8633)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.51  % (8636)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  % (8626)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f115,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.20/0.51    inference(resolution,[],[f22,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f8])).
% 0.20/0.51  fof(f8,conjecture,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.20/0.51    inference(forward_demodulation,[],[f114,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.20/0.51    inference(backward_demodulation,[],[f44,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f47,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    v2_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ~v2_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f41,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    v1_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.51    inference(resolution,[],[f22,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f43,f24])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ~v2_funct_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f33,f23])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    inference(resolution,[],[f22,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f113,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.51    inference(resolution,[],[f22,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f112,f22])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.51    inference(superposition,[],[f90,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k1_relat_1(sK0) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.51    inference(backward_demodulation,[],[f73,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.51    inference(forward_demodulation,[],[f87,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.20/0.51    inference(backward_demodulation,[],[f46,f48])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f45,f24])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ~v2_funct_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f34,f23])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    inference(resolution,[],[f22,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.51    inference(forward_demodulation,[],[f78,f50])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))),
% 0.20/0.51    inference(resolution,[],[f42,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f72,f42])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f71,f22])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.51    inference(superposition,[],[f52,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.51    inference(forward_demodulation,[],[f51,f48])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.51    inference(backward_demodulation,[],[f21,f48])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (8636)------------------------------
% 0.20/0.51  % (8636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8636)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (8636)Memory used [KB]: 1663
% 0.20/0.51  % (8636)Time elapsed: 0.096 s
% 0.20/0.51  % (8636)------------------------------
% 0.20/0.51  % (8636)------------------------------
% 0.20/0.51  % (8624)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (8622)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (8622)Refutation not found, incomplete strategy% (8622)------------------------------
% 0.20/0.51  % (8622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8622)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8622)Memory used [KB]: 6140
% 0.20/0.51  % (8622)Time elapsed: 0.107 s
% 0.20/0.51  % (8622)------------------------------
% 0.20/0.51  % (8622)------------------------------
% 0.20/0.52  % (8614)Success in time 0.157 s
%------------------------------------------------------------------------------
