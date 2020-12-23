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
% DateTime   : Thu Dec  3 12:54:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 118 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  144 ( 395 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(subsumption_resolution,[],[f275,f27])).

fof(f27,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f275,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f244,f191])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f179,f82])).

fof(f82,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X6,X4)
      | ~ r1_tarski(X4,X5)
      | r1_tarski(X6,X5) ) ),
    inference(resolution,[],[f80,f48])).

fof(f48,plain,(
    ! [X2,X1] :
      ( ~ v5_relat_1(k6_relat_1(X1),X2)
      | r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f47,f31])).

fof(f31,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f47,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k6_relat_1(X1)),X2)
      | ~ v5_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k6_relat_1(X2),X1)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f73,f45])).

fof(f45,plain,(
    ! [X2,X1] :
      ( v5_relat_1(k6_relat_1(X1),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f44,f31])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X1)),X2)
      | v5_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f33,f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X4,X2,X3] :
      ( ~ v5_relat_1(k6_relat_1(X4),X2)
      | ~ r1_tarski(X2,X3)
      | v5_relat_1(k6_relat_1(X4),X3) ) ),
    inference(resolution,[],[f35,f28])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ v5_relat_1(X2,X0)
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

fof(f179,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f158,f24])).

fof(f24,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f158,plain,(
    ! [X0] :
      ( ~ r1_tarski(k9_relat_1(sK2,sK0),X0)
      | r1_tarski(sK0,k10_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f155,f22])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f155,plain,(
    ! [X0] :
      ( r1_tarski(sK0,k10_relat_1(sK2,X0))
      | ~ r1_tarski(k9_relat_1(sK2,sK0),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f154,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f154,plain,(
    ! [X1] :
      ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X1)
      | r1_tarski(sK0,X1) ) ),
    inference(resolution,[],[f94,f25])).

fof(f25,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f91,f82])).

fof(f91,plain,(
    ! [X0] :
      ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
      | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f32,f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f244,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
    inference(subsumption_resolution,[],[f243,f26])).

fof(f26,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f243,plain,(
    ! [X0] :
      ( ~ v2_funct_1(sK2)
      | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ) ),
    inference(subsumption_resolution,[],[f242,f22])).

fof(f242,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ v2_funct_1(sK2)
      | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ) ),
    inference(resolution,[],[f36,f23])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:38:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (21367)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.47  % (21360)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.48  % (21355)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (21367)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f275,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f9])).
% 0.20/0.49  fof(f9,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(resolution,[],[f244,f191])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),X0) | r1_tarski(sK0,X0)) )),
% 0.20/0.49    inference(resolution,[],[f179,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X6,X4,X5] : (~r1_tarski(X6,X4) | ~r1_tarski(X4,X5) | r1_tarski(X6,X5)) )),
% 0.20/0.49    inference(resolution,[],[f80,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~v5_relat_1(k6_relat_1(X1),X2) | r1_tarski(X1,X2)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f47,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k6_relat_1(X1)),X2) | ~v5_relat_1(k6_relat_1(X1),X2)) )),
% 0.20/0.49    inference(resolution,[],[f34,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v5_relat_1(k6_relat_1(X2),X1) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X0)) )),
% 0.20/0.49    inference(resolution,[],[f73,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X1] : (v5_relat_1(k6_relat_1(X1),X2) | ~r1_tarski(X1,X2)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f44,f31])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X1)),X2) | v5_relat_1(k6_relat_1(X1),X2)) )),
% 0.20/0.49    inference(resolution,[],[f33,f28])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (~v5_relat_1(k6_relat_1(X4),X2) | ~r1_tarski(X2,X3) | v5_relat_1(k6_relat_1(X4),X3)) )),
% 0.20/0.49    inference(resolution,[],[f35,f28])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~v5_relat_1(X2,X0) | v5_relat_1(X2,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | (~v5_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))),
% 0.20/0.49    inference(resolution,[],[f158,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,sK0),X0) | r1_tarski(sK0,k10_relat_1(sK2,X0))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f155,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    v1_relat_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(sK0,k10_relat_1(sK2,X0)) | ~r1_tarski(k9_relat_1(sK2,sK0),X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.49    inference(resolution,[],[f154,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    ( ! [X1] : (~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X1) | r1_tarski(sK0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f94,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f91,f82])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) | ~r1_tarski(X0,k1_relat_1(sK2))) )),
% 0.20/0.49    inference(resolution,[],[f32,f22])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.20/0.49  fof(f244,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f243,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    v2_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_funct_1(sK2) | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f242,f22])).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(sK2) | ~v2_funct_1(sK2) | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) )),
% 0.20/0.49    inference(resolution,[],[f36,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (21367)------------------------------
% 0.20/0.49  % (21367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21367)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (21367)Memory used [KB]: 10746
% 0.20/0.49  % (21367)Time elapsed: 0.059 s
% 0.20/0.49  % (21367)------------------------------
% 0.20/0.49  % (21367)------------------------------
% 0.20/0.49  % (21338)Success in time 0.141 s
%------------------------------------------------------------------------------
