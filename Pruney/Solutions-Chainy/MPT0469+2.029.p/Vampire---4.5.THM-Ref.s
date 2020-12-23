%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:37 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   38 (  69 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 142 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f56])).

fof(f56,plain,(
    k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f18,f52])).

fof(f52,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f35,f20])).

fof(f20,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f24,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK4(X0,sK0(k2_relat_1(X0))),sK0(k2_relat_1(X0))),X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(resolution,[],[f31,f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f18,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f59,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f57,f36])).

fof(f57,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f50,f52])).

fof(f50,plain,
    ( r2_hidden(sK2(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f39,f33])).

fof(f33,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f22,f19])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0),k2_relat_1(X0))
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f26,f23])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(sK2(X1),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:54:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (779026433)
% 0.14/0.37  ipcrm: permission denied for id (779059203)
% 0.14/0.37  ipcrm: permission denied for id (779091973)
% 0.14/0.38  ipcrm: permission denied for id (779288587)
% 0.14/0.38  ipcrm: permission denied for id (779354127)
% 0.14/0.38  ipcrm: permission denied for id (779386896)
% 0.14/0.38  ipcrm: permission denied for id (779419665)
% 0.14/0.39  ipcrm: permission denied for id (779649047)
% 0.14/0.40  ipcrm: permission denied for id (779747354)
% 0.14/0.40  ipcrm: permission denied for id (779812892)
% 0.14/0.41  ipcrm: permission denied for id (779976740)
% 0.21/0.42  ipcrm: permission denied for id (780107818)
% 0.21/0.42  ipcrm: permission denied for id (780140588)
% 0.21/0.42  ipcrm: permission denied for id (780271664)
% 0.21/0.43  ipcrm: permission denied for id (780435510)
% 0.21/0.43  ipcrm: permission denied for id (780468280)
% 0.21/0.44  ipcrm: permission denied for id (780501050)
% 0.21/0.44  ipcrm: permission denied for id (780533820)
% 0.21/0.44  ipcrm: permission denied for id (780599359)
% 0.21/0.45  ipcrm: permission denied for id (780664900)
% 0.21/0.45  ipcrm: permission denied for id (780697669)
% 0.21/0.45  ipcrm: permission denied for id (780795978)
% 0.21/0.46  ipcrm: permission denied for id (780828747)
% 0.21/0.46  ipcrm: permission denied for id (780861516)
% 0.21/0.46  ipcrm: permission denied for id (780959822)
% 0.21/0.46  ipcrm: permission denied for id (780992591)
% 0.21/0.46  ipcrm: permission denied for id (781025361)
% 0.21/0.47  ipcrm: permission denied for id (781090899)
% 0.21/0.47  ipcrm: permission denied for id (781189206)
% 0.21/0.48  ipcrm: permission denied for id (781320282)
% 0.21/0.48  ipcrm: permission denied for id (781418591)
% 0.21/0.49  ipcrm: permission denied for id (781516898)
% 0.21/0.49  ipcrm: permission denied for id (781549667)
% 0.21/0.49  ipcrm: permission denied for id (781582436)
% 0.21/0.49  ipcrm: permission denied for id (781647973)
% 0.21/0.49  ipcrm: permission denied for id (781713511)
% 0.21/0.50  ipcrm: permission denied for id (781844588)
% 0.21/0.50  ipcrm: permission denied for id (781942896)
% 0.21/0.50  ipcrm: permission denied for id (781975665)
% 0.21/0.51  ipcrm: permission denied for id (782041205)
% 0.21/0.51  ipcrm: permission denied for id (782073974)
% 0.21/0.52  ipcrm: permission denied for id (782205050)
% 0.21/0.52  ipcrm: permission denied for id (782270589)
% 0.87/0.62  % (19334)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.87/0.63  % (19341)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.87/0.63  % (19347)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.87/0.64  % (19341)Refutation not found, incomplete strategy% (19341)------------------------------
% 0.87/0.64  % (19341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.87/0.64  % (19344)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.87/0.64  % (19335)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.87/0.64  % (19336)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.87/0.64  % (19341)Termination reason: Refutation not found, incomplete strategy
% 0.87/0.64  
% 0.87/0.64  % (19341)Memory used [KB]: 10618
% 0.87/0.64  % (19341)Time elapsed: 0.069 s
% 0.87/0.64  % (19341)------------------------------
% 0.87/0.64  % (19341)------------------------------
% 1.15/0.65  % (19347)Refutation found. Thanks to Tanya!
% 1.15/0.65  % SZS status Theorem for theBenchmark
% 1.15/0.65  % SZS output start Proof for theBenchmark
% 1.15/0.65  fof(f60,plain,(
% 1.15/0.65    $false),
% 1.15/0.65    inference(subsumption_resolution,[],[f59,f56])).
% 1.15/0.65  fof(f56,plain,(
% 1.15/0.65    k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.15/0.65    inference(subsumption_resolution,[],[f18,f52])).
% 1.15/0.65  fof(f52,plain,(
% 1.15/0.65    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.15/0.65    inference(resolution,[],[f40,f36])).
% 1.15/0.65  fof(f36,plain,(
% 1.15/0.65    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.15/0.65    inference(subsumption_resolution,[],[f35,f20])).
% 1.15/0.65  fof(f20,plain,(
% 1.15/0.65    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.15/0.65    inference(cnf_transformation,[],[f5])).
% 1.15/0.65  fof(f5,axiom,(
% 1.15/0.65    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.15/0.65  fof(f35,plain,(
% 1.15/0.65    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.15/0.65    inference(superposition,[],[f24,f21])).
% 1.15/0.65  fof(f21,plain,(
% 1.15/0.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.15/0.65    inference(cnf_transformation,[],[f4])).
% 1.15/0.65  fof(f4,axiom,(
% 1.15/0.65    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.15/0.65  fof(f24,plain,(
% 1.15/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.15/0.65    inference(cnf_transformation,[],[f15])).
% 1.15/0.65  fof(f15,plain,(
% 1.15/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.15/0.65    inference(ennf_transformation,[],[f11])).
% 1.15/0.65  fof(f11,plain,(
% 1.15/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.15/0.65    inference(rectify,[],[f2])).
% 1.15/0.65  fof(f2,axiom,(
% 1.15/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.15/0.65  fof(f40,plain,(
% 1.15/0.65    ( ! [X0] : (r2_hidden(k4_tarski(sK4(X0,sK0(k2_relat_1(X0))),sK0(k2_relat_1(X0))),X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 1.15/0.65    inference(resolution,[],[f31,f23])).
% 1.15/0.65  fof(f23,plain,(
% 1.15/0.65    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.15/0.65    inference(cnf_transformation,[],[f14])).
% 1.15/0.65  fof(f14,plain,(
% 1.15/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.15/0.65    inference(ennf_transformation,[],[f3])).
% 1.15/0.65  fof(f3,axiom,(
% 1.15/0.65    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.15/0.65  fof(f31,plain,(
% 1.15/0.65    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)) )),
% 1.15/0.65    inference(equality_resolution,[],[f28])).
% 1.15/0.65  fof(f28,plain,(
% 1.15/0.65    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.15/0.65    inference(cnf_transformation,[],[f7])).
% 1.15/0.65  fof(f7,axiom,(
% 1.15/0.65    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.15/0.65  fof(f18,plain,(
% 1.15/0.65    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 1.15/0.65    inference(cnf_transformation,[],[f12])).
% 1.15/0.65  fof(f12,plain,(
% 1.15/0.65    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.15/0.65    inference(ennf_transformation,[],[f10])).
% 1.15/0.65  fof(f10,negated_conjecture,(
% 1.15/0.65    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 1.15/0.65    inference(negated_conjecture,[],[f9])).
% 1.15/0.65  fof(f9,conjecture,(
% 1.15/0.65    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.15/0.65  fof(f59,plain,(
% 1.15/0.65    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.15/0.65    inference(subsumption_resolution,[],[f57,f36])).
% 1.15/0.65  fof(f57,plain,(
% 1.15/0.65    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.15/0.65    inference(backward_demodulation,[],[f50,f52])).
% 1.15/0.65  fof(f50,plain,(
% 1.15/0.65    r2_hidden(sK2(k1_xboole_0),k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.15/0.65    inference(resolution,[],[f39,f33])).
% 1.15/0.65  fof(f33,plain,(
% 1.15/0.65    v1_relat_1(k1_xboole_0)),
% 1.15/0.65    inference(resolution,[],[f22,f19])).
% 1.15/0.65  fof(f19,plain,(
% 1.15/0.65    v1_xboole_0(k1_xboole_0)),
% 1.15/0.65    inference(cnf_transformation,[],[f1])).
% 1.15/0.65  fof(f1,axiom,(
% 1.15/0.65    v1_xboole_0(k1_xboole_0)),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.15/0.65  fof(f22,plain,(
% 1.15/0.65    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.15/0.65    inference(cnf_transformation,[],[f13])).
% 1.15/0.65  fof(f13,plain,(
% 1.15/0.65    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.15/0.65    inference(ennf_transformation,[],[f6])).
% 1.15/0.65  fof(f6,axiom,(
% 1.15/0.65    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.15/0.65  fof(f39,plain,(
% 1.15/0.65    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(sK2(X0),k2_relat_1(X0)) | k1_xboole_0 = k1_relat_1(X0)) )),
% 1.15/0.65    inference(resolution,[],[f26,f23])).
% 1.15/0.65  fof(f26,plain,(
% 1.15/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | r2_hidden(sK2(X1),k2_relat_1(X1))) )),
% 1.15/0.65    inference(cnf_transformation,[],[f17])).
% 1.15/0.65  fof(f17,plain,(
% 1.15/0.65    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.15/0.65    inference(flattening,[],[f16])).
% 1.15/0.65  fof(f16,plain,(
% 1.15/0.65    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.15/0.65    inference(ennf_transformation,[],[f8])).
% 1.15/0.65  fof(f8,axiom,(
% 1.15/0.65    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 1.15/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).
% 1.15/0.65  % SZS output end Proof for theBenchmark
% 1.15/0.65  % (19347)------------------------------
% 1.15/0.65  % (19347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.65  % (19347)Termination reason: Refutation
% 1.15/0.65  
% 1.15/0.65  % (19347)Memory used [KB]: 1663
% 1.15/0.65  % (19347)Time elapsed: 0.086 s
% 1.15/0.65  % (19347)------------------------------
% 1.15/0.65  % (19347)------------------------------
% 1.15/0.65  % (19191)Success in time 0.291 s
%------------------------------------------------------------------------------
