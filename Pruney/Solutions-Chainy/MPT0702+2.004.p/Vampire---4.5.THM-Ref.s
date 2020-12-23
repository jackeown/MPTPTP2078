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
% DateTime   : Thu Dec  3 12:54:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 105 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  134 ( 372 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f457,plain,(
    $false ),
    inference(subsumption_resolution,[],[f448,f263])).

fof(f263,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(resolution,[],[f47,f26])).

fof(f26,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) ) ),
    inference(resolution,[],[f23,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

% (4340)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (4323)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (4320)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% (4332)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (4321)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f448,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(resolution,[],[f406,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(k2_tarski(X0,sK1)))
      | ~ r1_tarski(sK0,X1) ) ),
    inference(superposition,[],[f123,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f123,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,k1_setfam_1(k2_tarski(sK1,X6)))
      | ~ r1_tarski(sK0,X5) ) ),
    inference(resolution,[],[f67,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f67,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,sK1)
      | ~ r1_tarski(sK0,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f56,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f28,f39])).

fof(f28,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f406,plain,(
    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(superposition,[],[f55,f393])).

fof(f393,plain,(
    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(superposition,[],[f53,f73])).

fof(f73,plain,(
    k9_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f25,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f25,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(subsumption_resolution,[],[f52,f24])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) ),
    inference(subsumption_resolution,[],[f50,f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) ),
    inference(resolution,[],[f27,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f38,f31,f31])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(f27,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X2)),X2) ),
    inference(subsumption_resolution,[],[f54,f24])).

fof(f54,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK2)
      | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X2)),X2) ) ),
    inference(subsumption_resolution,[],[f51,f23])).

fof(f51,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X2)),X2) ) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:46:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (4327)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.49  % (4318)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.49  % (4343)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.50  % (4341)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (4335)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (4322)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (4335)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f457,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f448,f263])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.21/0.53    inference(resolution,[],[f47,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) )),
% 0.21/0.53    inference(resolution,[],[f23,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  % (4340)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (4323)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (4320)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (4332)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (4321)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  fof(f448,plain,(
% 0.21/0.54    ~r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.21/0.54    inference(resolution,[],[f406,f132])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,k1_setfam_1(k2_tarski(X0,sK1))) | ~r1_tarski(sK0,X1)) )),
% 0.21/0.54    inference(superposition,[],[f123,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X6,X5] : (~r1_tarski(X5,k1_setfam_1(k2_tarski(sK1,X6))) | ~r1_tarski(sK0,X5)) )),
% 0.21/0.54    inference(resolution,[],[f67,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f29,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~r1_tarski(X1,sK1) | ~r1_tarski(sK0,X2) | ~r1_tarski(X2,X1)) )),
% 0.21/0.54    inference(resolution,[],[f56,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,sK1)) )),
% 0.21/0.54    inference(resolution,[],[f28,f39])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ~r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f406,plain,(
% 0.21/0.54    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1)))),
% 0.21/0.54    inference(superposition,[],[f55,f393])).
% 0.21/0.54  fof(f393,plain,(
% 0.21/0.54    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))),
% 0.21/0.54    inference(superposition,[],[f53,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    k9_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.21/0.54    inference(resolution,[],[f25,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f33,f31])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f52,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_funct_1(sK2) | k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f50,f23])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 0.21/0.55    inference(resolution,[],[f27,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f38,f31,f31])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(flattening,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    v2_funct_1(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X2] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X2)),X2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f54,f24])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2] : (~v1_funct_1(sK2) | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X2)),X2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f51,f23])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X2] : (~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X2)),X2)) )),
% 0.21/0.55    inference(resolution,[],[f27,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (4335)------------------------------
% 0.21/0.55  % (4335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4335)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (4335)Memory used [KB]: 2046
% 0.21/0.55  % (4335)Time elapsed: 0.120 s
% 0.21/0.55  % (4335)------------------------------
% 0.21/0.55  % (4335)------------------------------
% 1.41/0.55  % (4317)Success in time 0.181 s
%------------------------------------------------------------------------------
