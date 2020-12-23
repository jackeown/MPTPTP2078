%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  70 expanded)
%              Number of leaves         :    3 (  14 expanded)
%              Depth                    :   13
%              Number of atoms          :   78 ( 302 expanded)
%              Number of equality atoms :   13 (  81 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(subsumption_resolution,[],[f37,f19])).

% (13662)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f19,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f37,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f36,f11])).

fof(f11,plain,(
    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X1,k2_relat_1(X2))
            & r1_tarski(X0,k2_relat_1(X2))
            & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X1,k2_relat_1(X2))
          & r1_tarski(X0,k2_relat_1(X2))
          & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_1)).

fof(f36,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f10,f9,f12,f35,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

% (13656)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f35,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f14,f32,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f32,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f19,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f28,f13])).

fof(f13,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | ~ r1_tarski(sK1,k2_relat_1(sK2))
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f27,f9])).

fof(f27,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(sK1,k2_relat_1(sK2))
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f25,f10])).

fof(f25,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(sK1,k2_relat_1(sK2))
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f18,f11])).

fof(f14,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f6])).

fof(f12,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:21:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (13667)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (13670)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.55  % (13664)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (13668)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (13675)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  % (13659)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.55  % (13663)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (13672)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.55  % (13659)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f37,f19])).
% 0.22/0.55  % (13662)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0))),
% 0.22/0.55    inference(forward_demodulation,[],[f36,f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (X0 != X1 & r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.55    inference(flattening,[],[f5])).
% 0.22/0.55  fof(f5,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((X0 != X1 & (r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)) => X0 = X1))),
% 0.22/0.55    inference(negated_conjecture,[],[f3])).
% 0.22/0.55  fof(f3,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)) => X0 = X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_1)).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f10,f9,f12,f35,f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,k2_relat_1(X2)) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k2_relat_1(X2)) | ~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(flattening,[],[f7])).
% 0.22/0.55  fof(f7,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~r1_tarski(X0,k2_relat_1(X2)) | ~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  % (13656)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ~r1_tarski(sK0,sK1)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f14,f32,f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    r1_tarski(sK1,sK0)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f19,f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0)) | r1_tarski(sK1,X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f28,f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    r1_tarski(sK1,k2_relat_1(sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0)) | ~r1_tarski(sK1,k2_relat_1(sK2)) | r1_tarski(sK1,X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f27,f9])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0)) | ~v1_relat_1(sK2) | ~r1_tarski(sK1,k2_relat_1(sK2)) | r1_tarski(sK1,X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f25,f10])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(sK1,k2_relat_1(sK2)) | r1_tarski(sK1,X0)) )),
% 0.22/0.55    inference(superposition,[],[f18,f11])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    sK0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    v1_relat_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (13659)------------------------------
% 0.22/0.55  % (13659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13659)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (13659)Memory used [KB]: 1663
% 0.22/0.55  % (13659)Time elapsed: 0.123 s
% 0.22/0.55  % (13659)------------------------------
% 0.22/0.55  % (13659)------------------------------
% 0.22/0.56  % (13676)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.56  % (13654)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.56  % (13655)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.56  % (13651)Success in time 0.187 s
%------------------------------------------------------------------------------
